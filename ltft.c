/*
	SECU-3  - An open source, free engine control unit
	Copyright (C) 2007 Alexey A. Shabelnikov. Ukraine, Kiev

	This program is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	This program is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with this program.  If not, see <http://www.gnu.org/licenses/>.

	contacts:
		http://secu-3.org
		email: shabelnikov@secu-3.org
	file ltft.c
	author Alexey A. Shabelnikov
	Implementation of the long term fuel trim algorithm
*/

#ifdef FUEL_INJECT

#include "port/port.h"
#include "port/pgmspace.h"
#include <stdlib.h>
#include "ltft.h"
#include "ecudata.h"
#include "eeprom.h"
#include "suspendop.h"
#include "funconv.h"
#include "lambda.h"
#include "mathemat.h"
#include "bitmask.h"

// Режим отладки
//#define DEBUG_MODE
// Размер буфера
#define KOSH_CBS 20

// =============================================================================
// ============ Костыль для коррекции ячеек с помощью интерполяции =============
// =============================================================================

// Вытащил эти макросы из funconv.c
#define secu3_offsetof(type,member)   ((size_t)(&((type *)0)->member))
#define _GWU12(x,i,j) (d.mm_ptr12(secu3_offsetof(struct f_data_t, x), (i*16+j) ))

// Структура для хранения переменных
typedef struct {
	uint16_t RPM;					// Обороты x1
	uint16_t MAP;					// Давление x64
	uint16_t Kf;					// Коэффициент выравнивания x64
	uint8_t x1;						// Координаты рабочих ячеек Обороты
	uint8_t x2;						// -//-
	uint8_t y1;						// Координаты рабочих ячеек Давление
	uint8_t y2;						// -//-
	uint16_t StartVE[4];			// Начальные значения VE x2048
	uint16_t LTFTVE[4];				// Значения VE с текущей коррекцией LTFT x2048
	uint16_t CalcVE;				// Интерполяция начальной VE x2048
	uint16_t TargetVe;				// Целевое VE x2048
	uint16_t CellsProp[4];			// Вес ячеек в коррекции x2048
	int16_t VEAlignment[4];			// Добавка для выравнивания ячеек x2048
	int16_t AddVE[4];				// Добавка к VE по коррекции x2048
	int16_t LTFTAdd[4];				// Добавочный коэффициент LTFT x512
	uint16_t BufferRPM[KOSH_CBS];	// Кольцевой буфер оборотов
	uint16_t BufferMAP[KOSH_CBS];	// Кольцевой буфер давления
	uint8_t BufferIndex;			// Текущая позиция буфера
	uint8_t BufferAvg;				// Текущая позиция усреднения
	uint32_t BufferSumRPM;			// Переменная для суммирования оборотов
	uint32_t BufferSumMAP;			// Переменная для суммирования давления
	int16_t StepMAP;      			// Шаг сетки давления при использовании двух значений
} Kosh_t;

// Инициализация структуры
Kosh_t Kosh = {
				.RPM = 0,
				.MAP = 0,
				.Kf = 0,
				.x1 = 0,
				.x2 = 0,
				.y1 = 0,
				.y2 = 0,
				.StartVE = {0},
				.LTFTVE = {0},
				.CalcVE = 0,
				.TargetVe = 0,
				.CellsProp = {0},
				.VEAlignment = {0},
				.AddVE = {0},
				.LTFTAdd = {0},
				.BufferRPM = {0},
				.BufferMAP = {0},
				.BufferIndex = 0,
				.BufferAvg = 0,
				.BufferSumRPM = 0,
				.BufferSumMAP = 0,
				.StepMAP = 0
			};

// PGM_GET_BYTE(&fw_data.exdata.inj_aftstr_strk1[fcs.ta_i])
// Порядок нумерации ячеек в массивах
//	1  2
//	0  3

// Расчет коррекции 
void kosh_ltft_control(uint8_t Channel) {
	#ifdef DEBUG_MODE
		// Обороты, давление и лямбда коррекция
		// для отладки будут браться из VE
		// Обороты VE * 2
		Kosh.RPM = _GWU12(inj_ve2, 14, 0) << 1;
		// Давление VE * 4
		Kosh.MAP = _GWU12(inj_ve2, 14, 1) << 2;
		// Лямбда коррекция
		d.corr.lambda[Channel] = (_GWU12(inj_ve2, 14, 2) >> 4) - 128;

		for (uint8_t i = 0; i < 16; ++i) {
			d.inj_ltft2[0][i] = PGM_GET_BYTE(&fw_data.exdata.inj_aftstr_strk1[i]);
			d.inj_ltft2[1][i] = (PGM_GET_BYTE(&fw_data.exdata.inj_aftstr_strk1[i])) >> 1;
			int8_t Index = (PGM_GET_BYTE(&fw_data.exdata.inj_aftstr_strk1[i])) >> 2;
			d.inj_ltft2[2][i] = Index;
		}
	#else
		// Уходим, пока не накопится коррекция
		if (d.corr.lambda[Channel] > -3 && d.corr.lambda[Channel] < 3) {return;}

		// Находим целевые обороты и давления с учетом задержки
		kosh_rpm_map_calc();
	#endif

	// Пороги по оборотам и давлению (в основном для ХХ)
	if (Kosh.RPM < 1100 && Kosh.MAP < 35) {return;}

	// Флаг использовать сетку давления
	uint8_t use_grid = CHECKBIT(d.param.func_flags, FUNC_LDAX_GRID);
	if (!use_grid) {
		Kosh.StepMAP = (d.param.load_upper - d.param.load_lower) / 15;
	}
	else {
		Kosh.StepMAP = 0;
	}

	/*
	Kosh.StepMAP ? PGM_GET_WORD(&fw_data.exdata.load_grid_points[Kosh.y1]) : (Kosh.StepMAP * Kosh.y1 + d.param.load_lower),
	Kosh.StepMAP ? PGM_GET_WORD(&fw_data.exdata.load_grid_sizes[Kosh.y1]) : (Kosh.StepMAP),
	*/

	// Коэффициент выравнивания будет пока храниться в таблице VE2
	// в левом верхнем углу, x2048 -> x64
	Kosh.Kf = _GWU12(inj_ve2, 15, 0) >> 5;

	// Поиск задействованных ячеек в расчете
	kosh_find_cells();

	#ifdef DEBUG_MODE
		// Обнуление LTFT в рабочих ячейках
		d.inj_ltft1[Kosh.y1][Kosh.x1] = 0;
		d.inj_ltft1[Kosh.y2][Kosh.x1] = 0;
		d.inj_ltft1[Kosh.y2][Kosh.x2] = 0;
		d.inj_ltft1[Kosh.y1][Kosh.x2] = 0;
	#endif
	
	// Извлечение значений из таблицы VE
	Kosh.StartVE[0] = _GWU12(inj_ve, Kosh.y1, Kosh.x1);
	Kosh.StartVE[1] = _GWU12(inj_ve, Kosh.y2, Kosh.x1);
	Kosh.StartVE[2] = _GWU12(inj_ve, Kosh.y2, Kosh.x2);
	Kosh.StartVE[3] = _GWU12(inj_ve, Kosh.y1, Kosh.x2);
	
	// Вычисление значений с учетом имеющейся коррекции LTFT
	if (Channel) {
		Kosh.LTFTVE[0] = ((uint32_t) Kosh.StartVE[0] * (512 + d.inj_ltft2[Kosh.y1][Kosh.x1])) >> 9;
		Kosh.LTFTVE[1] = ((uint32_t) Kosh.StartVE[1] * (512 + d.inj_ltft2[Kosh.y2][Kosh.x1])) >> 9;
		Kosh.LTFTVE[2] = ((uint32_t) Kosh.StartVE[2] * (512 + d.inj_ltft2[Kosh.y2][Kosh.x2])) >> 9;
		Kosh.LTFTVE[3] = ((uint32_t) Kosh.StartVE[3] * (512 + d.inj_ltft2[Kosh.y1][Kosh.x2])) >> 9;
	}
	else {
		Kosh.LTFTVE[0] = ((uint32_t) Kosh.StartVE[0] * (512 + d.inj_ltft1[Kosh.y1][Kosh.x1])) >> 9;
		Kosh.LTFTVE[1] = ((uint32_t) Kosh.StartVE[1] * (512 + d.inj_ltft1[Kosh.y2][Kosh.x1])) >> 9;
		Kosh.LTFTVE[2] = ((uint32_t) Kosh.StartVE[2] * (512 + d.inj_ltft1[Kosh.y2][Kosh.x2])) >> 9;
		Kosh.LTFTVE[3] = ((uint32_t) Kosh.StartVE[3] * (512 + d.inj_ltft1[Kosh.y1][Kosh.x2])) >> 9;
	}

	// Расчет веса точек в коррекции
	kosh_points_weight();

	Kosh.CalcVE = bilinear_interpolation(Kosh.RPM, Kosh.MAP,
								Kosh.LTFTVE[0],
								Kosh.LTFTVE[1],
								Kosh.LTFTVE[2], 
								Kosh.LTFTVE[3],
								PGM_GET_WORD(&fw_data.exdata.rpm_grid_points[Kosh.x1]),
								PGM_GET_WORD(&fw_data.exdata.load_grid_points[Kosh.y1]),
								PGM_GET_WORD(&fw_data.exdata.rpm_grid_sizes[Kosh.x1]),
								PGM_GET_WORD(&fw_data.exdata.load_grid_sizes[Kosh.y1]),
								1);

	// Целевое VE 
	Kosh.TargetVe = ((uint32_t) Kosh.CalcVE * (512 + d.corr.lambda[Channel])) >> 9;
	Kosh.TargetVe += 1;

	// Расчет добавки для выравнивания ячеек
	int8_t Ng = 1;
	for (uint8_t i = 0; i < 4; ++i) {
		// Тут может быть орицательное цисло, и сдвигать биты в этом случае -
		// это плохая идея, потому минус добавляем в конце.
		Ng = 1;
		Kosh.VEAlignment[i] = Kosh.TargetVe - Kosh.LTFTVE[i];
		if (Kosh.VEAlignment[i] < 0) {
			Ng = -1;
			Kosh.VEAlignment[i] *= Ng;
		}
		Kosh.VEAlignment[i] = ((uint32_t) Kosh.VEAlignment[i] * Kosh.CellsProp[i]) >> 11;
		Kosh.VEAlignment[i] = ((uint32_t) Kosh.VEAlignment[i] * Kosh.Kf) >> 6;
		Kosh.VEAlignment[i] *= Ng;
	}

	// Расчет добавки по лямбде
	kosh_add_ve_calculate(Channel);

	// Итого мы имеем два массива значений VEAlignment и AddVE,
	// которые необходимо добавить к VE.
	// Мы их считали уже с учетом имеющейся коррекции LTFT.

	// Теперь надо найти процент добавки от начального значения VE (без LTFT)
	// и добавить к текущему значению LTFT.

	// Расчет добавочного коэффициента LTFT
	for (uint8_t i = 0; i < 4; ++i) {
		Kosh.LTFTAdd[i] = (int32_t) (Kosh.VEAlignment[i] + Kosh.AddVE[i]) * 512 / Kosh.StartVE[i];
	}

	kosh_write_value(Kosh.y1, Kosh.x1, 0, Channel);
	kosh_write_value(Kosh.y2, Kosh.x1, 1, Channel);
	kosh_write_value(Kosh.y2, Kosh.x2, 2, Channel);
	kosh_write_value(Kosh.y1, Kosh.x2, 3, Channel);

	// Обнуление лямбда коррекции
	d.corr.lambda[Channel] = 0;

	// Вывод для отладки
	#ifdef DEBUG_MODE
		for (uint8_t i = 0; i < 4; ++i) {
			d.inj_ltft1[15][i] = Kosh.VEAlignment[i] / 4;
			d.inj_ltft1[14][i] = Kosh.AddVE[i] / 4;
			d.inj_ltft1[13][i] = Kosh.LTFTAdd[i];
			d.inj_ltft1[12][i] = ((int32_t) Kosh.CellsProp[i] * 512 / 10) >> 11;
		}
		d.inj_ltft1[15][6] = (float) Kosh.CalcVE  * 0.025;
		d.inj_ltft1[14][6] = (float) Kosh.TargetVe  * 0.025;
	#endif
}

void kosh_write_value(uint8_t y, uint8_t x, uint8_t n, uint8_t Channel) {
	// Ограничение значения коррекции
	int16_t Value = Channel ? d.inj_ltft2[y][x] : d.inj_ltft1[y][x];
	int8_t Min = PGM_GET_BYTE(&fw_data.exdata.ltft_min);
	int8_t Max = PGM_GET_BYTE(&fw_data.exdata.ltft_max);

	if (Value + Kosh.LTFTAdd[n] > Max) {Kosh.LTFTAdd[n] = Max - Value;}
	else if (Value + Kosh.LTFTAdd[n] < Min) {Kosh.LTFTAdd[n] = Min - Value;}

	// Добавляем коррекцию в таблицу LTFT (Давление / Обороты)
	if (Channel) {d.inj_ltft2[y][x] += Kosh.LTFTAdd[n];}
	else 		 {d.inj_ltft1[y][x] += Kosh.LTFTAdd[n];}
}

// Поиск задействованных ячеек в расчете	
void kosh_find_cells(void) {
	// Чтобы убрать здесь и дальше исключительные ситуации,
	// когда обороты меньше сетки или попали точно в сетку и т.п.,
	// буду просто добавлять или отнимать единицу

	// Обороты
	if (Kosh.RPM <= PGM_GET_WORD(&fw_data.exdata.rpm_grid_points[0])) {
		Kosh.RPM = PGM_GET_WORD(&fw_data.exdata.rpm_grid_points[0]) + 1;
	}
	if (Kosh.RPM >= PGM_GET_WORD(&fw_data.exdata.rpm_grid_points[15])) {
		Kosh.RPM = PGM_GET_WORD(&fw_data.exdata.rpm_grid_points[15]) - 1;
	}

	for (uint8_t i = 1; i < 16; i++) {
		if (Kosh.RPM <= PGM_GET_WORD(&fw_data.exdata.rpm_grid_points[i])) {
			if (Kosh.RPM == PGM_GET_WORD(&fw_data.exdata.rpm_grid_points[i])) {
				Kosh.RPM -= 1;
			}
			Kosh.x1 = i - 1;
			Kosh.x2 = i;
			break;
		}
	}

	// Давление
	if (Kosh.MAP <= PGM_GET_WORD(&fw_data.exdata.load_grid_points[0])) {
		Kosh.MAP = PGM_GET_WORD(&fw_data.exdata.load_grid_points[0]) + 1;
	}
	if (Kosh.MAP >= PGM_GET_WORD(&fw_data.exdata.load_grid_points[15])) {
		Kosh.MAP = PGM_GET_WORD(&fw_data.exdata.load_grid_points[15]) - 1;
	}

	for (uint8_t i = 1; i < 16; i++) {
		if (Kosh.MAP <= PGM_GET_WORD(&fw_data.exdata.load_grid_points[i])) {
			if (Kosh.MAP == PGM_GET_WORD(&fw_data.exdata.load_grid_points[i])) {
				Kosh.MAP -= 1;
			}
			Kosh.y1 = i - 1;
			Kosh.y2 = i;
			break;
		}
	}
}

// Расчет веса точек в коррекции
void kosh_points_weight(void) {
	uint16_t x1 = PGM_GET_WORD(&fw_data.exdata.rpm_grid_points[Kosh.x1]);
	uint16_t x2 = PGM_GET_WORD(&fw_data.exdata.rpm_grid_points[Kosh.x2]);
	uint16_t y1 = PGM_GET_WORD(&fw_data.exdata.load_grid_points[Kosh.y1]);
	uint16_t y2 = PGM_GET_WORD(&fw_data.exdata.load_grid_points[Kosh.y2]);

	uint16_t x = Kosh.RPM;
	uint16_t y = Kosh.MAP;

	uint16_t CFx1 = 0; // x2048 << 11
	uint16_t CFx2 = 0; // x2048
	uint16_t CFy1 = 0; // x2048
	uint16_t CFy2 = 0; // x2048

	CFx1 = (uint32_t) (x2 - x) * 2048 / (x2 - x1);
	CFx2 = (uint32_t) (x - x1) * 2048 / (x2 - x1);
				
	CFy1 = (uint32_t) (y2 - y) * 2048 / (y2 - y1);
	CFy2 = (uint32_t) (y - y1) * 2048 / (y2 - y1);

	Kosh.CellsProp[0] = ((uint32_t) CFx1 * CFy1) >> 11;
	Kosh.CellsProp[1] = ((uint32_t) CFx1 * CFy2) >> 11;
	Kosh.CellsProp[2] = ((uint32_t) CFx2 * CFy2) >> 11;
	Kosh.CellsProp[3] = ((uint32_t) CFx2 * CFy1) >> 11;
}

// Расчет добавки к VE
void kosh_add_ve_calculate(uint8_t Channel) {
	// Значение ячейки VE * Коррекцию * Долю
	uint16_t G[4] = {0, 0, 0, 0};
	uint16_t SummDelta = 0;

	// Если сдвигать биты с отрицательными числами, это может плохо закончиться.
	// Потому d.corr.lambda[Channel] временно делаем положительным.
	int8_t Ng = 1;
	if (d.corr.lambda[Channel] < 0) {Ng = -1;}

	for (uint8_t i = 0; i < 4; ++i) {
		G[i] = ((int32_t) Kosh.LTFTVE[i] * d.corr.lambda[Channel] * Ng) >> 9;
		G[i] = ((uint32_t) G[i] * Kosh.CellsProp[i]) >> 11;
		// Сумма отклонения
		SummDelta += ((uint32_t) G[i] * Kosh.CellsProp[i]) >> 11;
	}

	uint16_t CalcVE2 = bilinear_interpolation(Kosh.RPM, Kosh.MAP,
									Kosh.LTFTVE[0] + Kosh.VEAlignment[0],
									Kosh.LTFTVE[1] + Kosh.VEAlignment[1],
									Kosh.LTFTVE[2] + Kosh.VEAlignment[2],
									Kosh.LTFTVE[3] + Kosh.VEAlignment[3],
									PGM_GET_WORD(&fw_data.exdata.rpm_grid_points[Kosh.x1]),
									PGM_GET_WORD(&fw_data.exdata.load_grid_points[Kosh.y1]),
									PGM_GET_WORD(&fw_data.exdata.rpm_grid_sizes[Kosh.x1]),
									PGM_GET_WORD(&fw_data.exdata.load_grid_sizes[Kosh.y1]),
									1);

	// Коэффициент отклонения от цели
	uint16_t Cf = (int32_t) abs(Kosh.TargetVe - CalcVE2) * 1024 / SummDelta;

	// Добавка к VE
	for (uint8_t i = 0; i < 4; ++i) {
		Kosh.AddVE[i] = ((uint32_t) G[i] * Cf) >> 10;
		Kosh.AddVE[i] *= Ng;
	}
}

// Вычисление оборотов и давления с учетом задержки
void kosh_rpm_map_calc(void) {
	// Берем последние 8 значений давления для вычисления среднего
	uint32_t MAPAVG = 0;
	for (uint8_t i = 0; i < 8; i++) {
		int8_t Index = Kosh.BufferIndex - i;
		if (Index < 0) {Index = KOSH_CBS + Index;}
		MAPAVG += Kosh.BufferMAP[Index];
	}

  	MAPAVG = MAPAVG >> 3;
  	if (MAPAVG > PGM_GET_WORD(&fw_data.exdata.load_grid_points[15])) {
  		MAPAVG = PGM_GET_WORD(&fw_data.exdata.load_grid_points[15]);
  	}
  	// Находим задержку из сетки
  	for (uint8_t i = 0; i < 16; i++) {
  		if (MAPAVG <= PGM_GET_WORD(&fw_data.exdata.load_grid_points[i])) {

  			// Значения лага хранятся в таблице "Такты ОПП (газ)"
  			int8_t Index = (PGM_GET_BYTE(&fw_data.exdata.inj_aftstr_strk1[i])) >> 2;
  			// Находим индекс оборотов и давления
  			Index = Kosh.BufferIndex - Index;
  			if (Index < 0) {Index = KOSH_CBS + Index;}

  			// Вытаскиваем оборотов и давления из прошлого
  			Kosh.RPM = Kosh.BufferRPM[Index];
  			Kosh.MAP = Kosh.BufferMAP[Index];
  			break;
  		}
 	}
}

// Обновление буфера
void kosh_circular_buffer_update(void) {
	Kosh.BufferSumRPM += d.sens.inst_frq;
	Kosh.BufferSumMAP += d.sens.inst_map;
	Kosh.BufferAvg++;

	// Достигнут предел усреднения
	if (Kosh.BufferAvg >= 4) {
		uint16_t RPM = Kosh.BufferSumRPM >> 2;
		Kosh.BufferRPM[Kosh.BufferIndex] = RPM;
		uint16_t MAP = Kosh.BufferSumMAP >> 2;
		Kosh.BufferMAP[Kosh.BufferIndex] = MAP;

		Kosh.BufferAvg = 0;
		Kosh.BufferSumRPM = 0;
		Kosh.BufferSumMAP = 0;

		Kosh.BufferIndex++;
		// Достигнут конец буфера
		if (Kosh.BufferIndex >= KOSH_CBS) {
			Kosh.BufferIndex = 0;
		}
	}
}

// =============================================================================
// =============================================================================
// =============================================================================

void ltft_control(void) {
	#ifdef DEBUG_MODE
		kosh_ltft_control(0);
	#endif

	// Условия выхода из функции:
	// 1 - Идет процесс записи в EEPROM
	uint8_t ee_opcode = eeprom_get_pending_opcode();
	if (ee_opcode == OPCODE_RESET_LTFT || ee_opcode == OPCODE_SAVE_LTFT) {return;}
	// 2 - Температура ОЖ ниже порога
	if (d.sens.temperat < ((int16_t)PGM_GET_WORD(&fw_data.exdata.ltft_learn_clt))) {return;}

	#ifndef SECU3T
		// 3 - Давление газа ниже порога
		if (d.sens.map2 < PGM_GET_WORD(&fw_data.exdata.ltft_learn_gpa)) {return;}
		// 4 - Дифференциальное давление газа ниже порога
		if (PGM_GET_WORD(&fw_data.exdata.ltft_learn_gpd) && ((d.sens.map2 - d.sens.map) < PGM_GET_WORD(&fw_data.exdata.ltft_learn_gpd))) {return;}
	#endif

	// 5 - Адаптация выключена для текущего топлива
	if (!ltft_is_active()) {return;}
	// 6 - Лямбда коррекция отключена
	if (!d.sens.carb && !CHECKBIT(d.param.inj_lambda_flags, LAMFLG_IDLCORR)) {return;}
	// 7 - Адаптация выключена на ХХ
	if (!d.sens.carb && !PGM_GET_BYTE(&fw_data.exdata.ltft_on_idling)) {return;}

	uint8_t chnum = (0x00!=d.param.lambda_selch) && !CHECKBIT(d.param.inj_lambda_flags, LAMFLG_MIXSEN) ? 2 : 1;
	uint8_t chbeg = (0xFF==d.param.lambda_selch) && !CHECKBIT(d.param.inj_lambda_flags, LAMFLG_MIXSEN);

	for (uint8_t i = chbeg; i < chnum; ++i) {
		// Переход к моей функции
		kosh_ltft_control(i);
	}
}

uint8_t ltft_is_active(void) {
	if (PGM_GET_BYTE(&fw_data.exdata.ltft_mode)==0)	{
		return 0; //LTFT functionality turned off
	}
	else if (PGM_GET_BYTE(&fw_data.exdata.ltft_mode)==1) {
		if (1==d.sens.gas)
			return 0; // LTFT enabled only for petrol
	}
	else if (PGM_GET_BYTE(&fw_data.exdata.ltft_mode)==2) {
		if (0==d.sens.gas)
			return 0; // LTFT enabled only for gas
	}
	return 1;
}

void ltft_stroke_event_notification(void) {
	kosh_circular_buffer_update();
}

// FUEL_INJECT
#endif
