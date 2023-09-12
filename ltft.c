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

// =============================================================================
// ============ Костыль для коррекции ячеек с помощью интерполяции =============
// =============================================================================

// Вытащил эти макросы из funconv.c
#define secu3_offsetof(type,member)   ((size_t)(&((type *)0)->member))
#define _GWU12(x,i,j) (d.mm_ptr12(secu3_offsetof(struct f_data_t, x), (i*16+j) )) //note: hard coded size of array


// Структура для хранения переменных
typedef struct {
	int16_t RPMGrid[16];			// Сетка оборотов x1
	int16_t PressureGrid[16];		// Сетка давления x64
	int16_t Kf;						// Коэффициент выравнивания x64
	uint8_t x1;						// Координаты рабочих ячеек Обороты
	uint8_t x2;						// -//-
	uint8_t y1;						// Координаты рабочих ячеек Давление
	uint8_t y2;						// -//-
	int16_t StartVE[4];				// Начальные значения VE x2048
	int16_t LTFTVE[4];				// Значения VE с текущей коррекцией LTFT x2048
	int16_t CalcVE;					// Интерполяция начальной VE x2048
	int16_t TargetVe;				// Целевое VE x2048
	int16_t CellsProp[4];			// Вес ячеек в коррекции x2048
	int16_t VEAlignment[4];			// Добавка для выравнивания ячеек x2048
	int16_t AddVE[4];				// Добавка к VE по коррекции x2048
	int16_t LTFTAdd[4];				// Добавочный коэффициент LTFT x512
} Kosh_t;

// Инициализация структуры
Kosh_t Kosh = {.RPMGrid = {900, 1100, 1300, 1500, 1700, 2000, 2300, 2600, 2900, 3200, 3500, 3800, 4100, 4500, 5000, 6000},
				.PressureGrid = {1280, 1920, 2560, 3200, 3840, 4480, 5120, 5760, 6400, 7040, 7680, 8320, 8960, 9600, 10560, 11520},
				.Kf = 0.0,
				.x1 = 0,
				.x2 = 0,
				.y1 = 0,
				.y2 = 0,
				.StartVE = {0, 0, 0, 0},
				.LTFTVE = {0, 0, 0, 0},
				.CalcVE = 0,
				.TargetVe = 0,
				.CellsProp = {0, 0, 0, 0},
				.VEAlignment = {0.0, 0.0, 0.0, 0.0},
				.AddVE = {0.0, 0.0, 0.0, 0.0},
				.LTFTAdd = {0, 0, 0, 0}
			};

// Порядок нумерации ячеек в массивах
//	1  2
//	0  3

// Расчет коррекции 
void kosh_ltft_control(void) {
	#ifdef DEBUG_MODE
		d.sens.frequen = 1385;
		d.sens.map = 2200;
		d.corr.lambda[0] = 10; // 41 / 512 = 0.08

		Kosh.Kf = 13; // 13 / 64 = 0.2
	#else
		// Коэффициент выравнивания будет пока храниться в таблице VE2
		// в левом верхнем углу. x2064 -> x64
		Kosh.Kf = _GWU12(inj_ve2, 15, 0) >> 5;
	#endif

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
	Kosh.LTFTVE[0] = ((int32_t) Kosh.StartVE[0] * (512 + d.inj_ltft1[Kosh.y1][Kosh.x1])) >> 9;
	Kosh.LTFTVE[1] = ((int32_t) Kosh.StartVE[1] * (512 + d.inj_ltft1[Kosh.y2][Kosh.x1])) >> 9;
	Kosh.LTFTVE[2] = ((int32_t) Kosh.StartVE[2] * (512 + d.inj_ltft1[Kosh.y2][Kosh.x2])) >> 9;
	Kosh.LTFTVE[3] = ((int32_t) Kosh.StartVE[3] * (512 + d.inj_ltft1[Kosh.y1][Kosh.x2])) >> 9;

	// Расчет веса точек в коррекции
	kosh_points_weight();

	Kosh.CalcVE = bilinear_interpolation(d.sens.frequen, d.sens.map,
								Kosh.LTFTVE[0],
								Kosh.LTFTVE[1],
								Kosh.LTFTVE[2], 
								Kosh.LTFTVE[3],
								Kosh.RPMGrid[Kosh.x1],
								Kosh.PressureGrid[Kosh.y1],
								Kosh.RPMGrid[Kosh.x2] - Kosh.RPMGrid[Kosh.x1],
								Kosh.PressureGrid[Kosh.y2] - Kosh.PressureGrid[Kosh.y1],
								1);

	// Целевое VE 
	Kosh.TargetVe = ((int32_t) Kosh.CalcVE * (512 + d.corr.lambda[0])) >> 9;
	Kosh.TargetVe += 1;

	// Расчет добавки для выравнивания ячеек
	for (uint8_t i = 0; i < 4; ++i) {
		Kosh.VEAlignment[i] = Kosh.TargetVe - Kosh.LTFTVE[i];
		Kosh.VEAlignment[i] = ((int32_t) Kosh.VEAlignment[i] * Kosh.CellsProp[i]) >> 11;
		Kosh.VEAlignment[i] = ((int32_t) Kosh.VEAlignment[i] * Kosh.Kf) >> 6;
	}

	// Расчет добавки по лямбде
	kosh_add_ve_calculate();

	// Итого мы имеем два массива значений VEAlignment и AddVE,
	// которые необходимо добавить к VE.
	// Мы их считали уже с учетом имеющейся коррекции LTFT.

	// Теперь надо найти процент добавки от начального значения VE (без LTFT)
	// и добавить к текущему значению LTFT.

	// Расчет добавочного коэффициента LTFT
	for (uint8_t i = 0; i < 4; ++i) {
		Kosh.LTFTAdd[i] = (int32_t) (Kosh.VEAlignment[i] + Kosh.AddVE[i]) * 512 / Kosh.StartVE[i];
	}

	kosh_write_value(Kosh.y1, Kosh.x1, 0);
	kosh_write_value(Kosh.y2, Kosh.x1, 1);
	kosh_write_value(Kosh.y2, Kosh.x2, 2);
	kosh_write_value(Kosh.y1, Kosh.x2, 3);

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

void kosh_write_value(uint8_t y, uint8_t x, uint8_t n) {
	// Чтобы не перетерлись значения при совпадении оборотов или давления
	if (!Kosh.CellsProp[n]) {return;}

	// Ограничение значения коррекции  +-14 % (0.14 * 512 = 72)
	int16_t Value = 0;
	if (Value + Kosh.LTFTAdd[n] > 72) {Kosh.LTFTAdd[n] = 72 - Value;}
	else if (Value + Kosh.LTFTAdd[n] < -72) {Kosh.LTFTAdd[n] = -72 - Value;}

	// Добавляем коррекцию в таблицу LTFT (Давление / Обороты)
	d.inj_ltft1[y][x] += Kosh.LTFTAdd[n];
}

// Поиск задействованных ячеек в расчете	
void kosh_find_cells(void) {
	// Обороты
	if (d.sens.frequen <= Kosh.RPMGrid[0]) {
		Kosh.x1 = 0;
		Kosh.x2 = 0;
	}
	else if (d.sens.frequen >= Kosh.RPMGrid[15]) {
		Kosh.x1 = 15;
		Kosh.x2 = 15;
	}
	else {
		for (uint8_t i = 0; i < 15; ++i) {
			if (Kosh.RPMGrid[i] == d.sens.frequen) {
				Kosh.x1 = i;
				Kosh.x2 = i;
				break;
			}
			else if (d.sens.frequen < Kosh.RPMGrid[i]) {
				Kosh.x1 = i - 1;
				Kosh.x2 = i;
				break;
			}
		}
	}
	
	// Давление
	if (d.sens.map <= Kosh.PressureGrid[0]) {
		Kosh.y1 = 0;
		Kosh.y2 = 0;
	}
	else if (d.sens.map >= Kosh.PressureGrid[15]) {
		Kosh.y1 = 15;
		Kosh.y2 = 15;
	}
	else {
		for (uint8_t i = 0; i < 15; ++i) {
			if (Kosh.PressureGrid[i] == d.sens.map) {
				Kosh.y1 = i;
				Kosh.y2 = i;
				break;
			}
			else if (d.sens.map < Kosh.PressureGrid[i]) {
				Kosh.y1 = i - 1;
				Kosh.y2 = i;
				break;
			}
		}
	}
}

// Расчет веса точек в коррекции
void kosh_points_weight(void) {
	int16_t x1 = Kosh.RPMGrid[Kosh.x1];
	int16_t x2 = Kosh.RPMGrid[Kosh.x2];
	int16_t y1 = Kosh.PressureGrid[Kosh.y1];
	int16_t y2 = Kosh.PressureGrid[Kosh.y2];
	
	int16_t x = d.sens.frequen;
	int16_t y = d.sens.map;

	// Если обороты и давление точно попали в точку
	if (x2 == x1 && y2 == y1) {
		Kosh.CellsProp[0] = 2048;
		Kosh.CellsProp[1] = 0;
		Kosh.CellsProp[2] = 0;
		Kosh.CellsProp[3] = 0;
		return;
	}

	int16_t CFx1 = 0; // x2048 << 11
	int16_t CFx2 = 0; // x2048
	int16_t CFy1 = 0; // x2048
	int16_t CFy2 = 0; // x2048

	if (x2 != x1) {
		CFx1 = (int32_t) (x2 - x) * 2048 / (x2 - x1);
		CFx2 = (int32_t) (x - x1) * 2048 / (x2 - x1);
	}
				
	if (y2 != y1) {
		CFy1 = (int32_t) (y2 - y) * 2048 / (y2 - y1);
		CFy2 = (int32_t) (y - y1) * 2048 / (y2 - y1);
	}

	// Если обороты попали в точку
	if (x1 == x2) {
		Kosh.CellsProp[0] = CFy1;
		Kosh.CellsProp[1] = CFy2;
		Kosh.CellsProp[2] = 0.0;
		Kosh.CellsProp[3] = 0.0;
		return;
	}

	// Если давление попало в точку
	if (y1 == y2) {
		Kosh.CellsProp[0] = CFx1;
		Kosh.CellsProp[1] = 0.0;
		Kosh.CellsProp[2] = 0.0;
		Kosh.CellsProp[3] = CFx2;
		return;
	}

	Kosh.CellsProp[0] = ((int32_t) CFx1 * CFy1) >> 11;
	Kosh.CellsProp[1] = ((int32_t) CFx1 * CFy2) >> 11;
	Kosh.CellsProp[2] = ((int32_t) CFx2 * CFy2) >> 11;
	Kosh.CellsProp[3] = ((int32_t) CFx2 * CFy1) >> 11;
}

// Расчет добавки к VE
void kosh_add_ve_calculate(void) {
	// Значение ячейки VE * Коррекцию * Долю
	int16_t G[4] = {0, 0, 0, 0};
	int16_t SummDelta = 0;

	// Битовый сдвиг не работает с отрицательными числами,
	// Потому d.corr.lambda[0] временно делаем положительным.
	int8_t Ng = 1;
	if (d.corr.lambda[0] < 0) {Ng = -1;}

	for (uint8_t i = 0; i < 4; ++i) {
		G[i] = ((int32_t) Kosh.LTFTVE[i] * d.corr.lambda[0] * Ng) >> 9;
		G[i] = ((int32_t) G[i] * Kosh.CellsProp[i]) >> 11;
		// Сумма отклонения
		SummDelta += ((int32_t) G[i] * Kosh.CellsProp[i]) >> 11;
	}

	int16_t CalcVE2 = bilinear_interpolation(d.sens.frequen, d.sens.map,
									Kosh.LTFTVE[0] + Kosh.VEAlignment[0],
									Kosh.LTFTVE[1] + Kosh.VEAlignment[1],
									Kosh.LTFTVE[2] + Kosh.VEAlignment[2],
									Kosh.LTFTVE[3] + Kosh.VEAlignment[3],
									Kosh.RPMGrid[Kosh.x1],
									Kosh.PressureGrid[Kosh.y1],
									Kosh.RPMGrid[Kosh.x2] - Kosh.RPMGrid[Kosh.x1],
									Kosh.PressureGrid[Kosh.y2] - Kosh.PressureGrid[Kosh.y1],
									1);

	// Коэффициент отклонения от цели
	int16_t Cf = (int32_t) (Kosh.TargetVe - CalcVE2) * 1024 / SummDelta;

	// Добавка к VE
	for (uint8_t i = 0; i < 4; ++i) {
		Kosh.AddVE[i] = ((int32_t) G[i] * Cf * Ng) >> 10;
		Kosh.AddVE[i] = Kosh.AddVE[i] * Ng;
	}
}

// =============================================================================
// =============================================================================
// =============================================================================



/**Describes data for each LTFT channel*/
typedef struct {
	uint8_t ltft_state;  //!< SM state
	uint16_t stat_tmr;   //!< timer
	uint8_t ltft_idx_r;  //!< rpm index of current work point
	uint8_t ltft_idx_l;  //!< load index of current work point
	int16_t ltft_corr;   //!< value of actual correction
	uint8_t idx_l;       //!< index for iteration throught load axis
	uint8_t idx_r;       //!< index for iteration throught rpm axis
	uint8_t strokes;     //!< counter of eng. strokes
} ltft_t;

ltft_t ltft[2] = {{0,0,0,0,0,0,0,0},{0,0,0,0,0,0,0,0}};

void ltft_control(void) {
	#ifdef DEBUG_MODE
		kosh_ltft_control();
	#endif

	uint8_t ee_opcode = eeprom_get_pending_opcode();
	if (ee_opcode == OPCODE_RESET_LTFT || ee_opcode == OPCODE_SAVE_LTFT)
		return; //do not write to LTFT map during saving to EEPROM

	if (d.sens.temperat < ((int16_t)PGM_GET_WORD(&fw_data.exdata.ltft_learn_clt)))
		return; //CLT is too low for learning

	#ifndef SECU3T
		if (d.sens.map2 < PGM_GET_WORD(&fw_data.exdata.ltft_learn_gpa))
			return; //gas pressure is below threshold

		if (PGM_GET_WORD(&fw_data.exdata.ltft_learn_gpd) && ((d.sens.map2 - d.sens.map) < PGM_GET_WORD(&fw_data.exdata.ltft_learn_gpd)))
			return; //differential gas pressure is below threshold
	#endif

	if (!ltft_is_active())
		return; //LTFT functionality turned off or not active for current fuel

	if (!d.sens.carb && !CHECKBIT(d.param.inj_lambda_flags, LAMFLG_IDLCORR))
		return; //Lambda correction is disabled on idling

	if (!d.sens.carb && !PGM_GET_BYTE(&fw_data.exdata.ltft_on_idling))
		return; //LTFT updating on idling is disabled

	uint8_t chnum = (0x00!=d.param.lambda_selch) && !CHECKBIT(d.param.inj_lambda_flags, LAMFLG_MIXSEN) ? 2 : 1;
	uint8_t chbeg = (0xFF==d.param.lambda_selch) && !CHECKBIT(d.param.inj_lambda_flags, LAMFLG_MIXSEN);

	for (uint8_t i = chbeg; i < chnum; ++i) {
		//do learning:
		switch(ltft[i].ltft_state) {
	   		case 0:
			{ //wait for work point to enter restricted band around a cell
				uint8_t r = ltft_check_rpm_hit();
				uint8_t l = ltft_check_load_hit();
				if (r != 255 && l != 255) {
					lambda_reset_swt_counter(i);
					ltft[i].stat_tmr = s_timer_gtc();
					ltft[i].strokes = 0;
					ltft[i].ltft_state++;
				}
				else
					break;
			}

			case 1:
			{
				uint8_t r = ltft_check_rpm_hit();
				uint8_t l = ltft_check_load_hit();
				if (r == 255 || l == 255) { //work point came out restricted band - reset SM state
					ltft[i].ltft_state = 0;
					break;
				}

				uint8_t stab_time_ready = 0;

				if (0==PGM_GET_BYTE(&fw_data.exdata.ltft_stab_str))
					stab_time_ready = ((s_timer_gtc() - ltft[i].stat_tmr) >= PGM_GET_BYTE(&fw_data.exdata.ltft_stab_time)); //use time
				else
					stab_time_ready = ltft[i].strokes >= PGM_GET_BYTE(&fw_data.exdata.ltft_stab_str); //use eng. strokes

				if (stab_time_ready && lambda_get_swt_counter(i) >= PGM_GET_BYTE(&fw_data.exdata.ltft_sigswt_num)) {

					/*	
					// Текущее значение в таблице LTFT
					int16_t ltft_curr = i ? d.inj_ltft2[l][r] : d.inj_ltft1[l][r];
					// Новое значение
					int16_t new_val = ltft_curr + d.corr.lambda[i];
					// Ограничение нового значения
					restrict_value_to(&new_val, (int16_t)PGM_GET_BYTE(&fw_data.exdata.ltft_min), (int16_t)PGM_GET_BYTE(&fw_data.exdata.ltft_max));
					
					// Запись нового значения в таблицу
					if (i)
						d.inj_ltft2[l][r] = new_val;     // apply correction to current cell of LTFT 2
					else
						d.inj_ltft1[l][r] = new_val;     // apply correction to current cell of LTFT 1

					// Обновление значения текущей коррекции
					ltft[i].ltft_corr = new_val - ltft_curr;

					// Уменьшение ламбда корреции
					d.corr.lambda[i]-=ltft[i].ltft_corr;       // reduce current lambda by actual value of correction (taking into account possible min/max restriction)
					// Координаты скорректированной ячейки
					ltft[i].ltft_idx_r = r, ltft[i].ltft_idx_l = l; // remember indexes of current work point

					// Обнуление индексов циклов
					ltft[i].idx_l = 0, ltft[i].idx_r = 0;

					// Переход к следующему шагу
					ltft[i].ltft_state++;
					*/

					// Переход к моей функции
					kosh_ltft_control();

					// Обнуление лямбда коррекции
					d.corr.lambda[i] = 0;
					// Сброс состояния
					ltft[i].ltft_state = 0;

				}
				else {
					break;
				}
			}

			case 2: //perform correction of neighbour cells
			{
				uint8_t r = PGM_GET_BYTE(&fw_data.exdata.ltft_neigh_rad);
				uint8_t idx_l = ltft[i].idx_l, idx_r = ltft[i].idx_r;
				if ((abs8((int8_t)idx_r - ltft[i].ltft_idx_r) <= r) && (abs8((int8_t)idx_l - ltft[i].ltft_idx_l) <= r)) { //skip cells which lay out of radius

					if (ltft[i].ltft_idx_r != idx_r || ltft[i].ltft_idx_l != idx_l) { //skip already corrected (current) cell
						int8_t dist_l = abs(ltft[i].ltft_idx_l - idx_l);
						int8_t dist_r = abs(ltft[i].ltft_idx_r - idx_r);
						int8_t dist = (dist_l > dist_r) ? dist_l : dist_r; //find maximum distance
						int16_t new_val = ((int16_t)(i ? d.inj_ltft2[idx_l][idx_r] : d.inj_ltft1[idx_l][idx_r])) + (((((int32_t)ltft[i].ltft_corr) * PGM_GET_BYTE(&fw_data.exdata.ltft_learn_grad)) >> 8) / dist);
						restrict_value_to(&new_val, (int16_t)PGM_GET_BYTE(&fw_data.exdata.ltft_min), (int16_t)PGM_GET_BYTE(&fw_data.exdata.ltft_max));
						
						if (i)
							d.inj_ltft2[idx_l][idx_r] = new_val;
						else
							d.inj_ltft1[idx_l][idx_r] = new_val;
					}
				}

				ltft[i].idx_r++;
				if (ltft[i].idx_r == INJ_VE_POINTS_F) {
					ltft[i].idx_r = 0;
					ltft[i].idx_l++;
				
					if (ltft[i].idx_l == INJ_VE_POINTS_L)
						ltft[i].ltft_state = 0; //all 256 cells updated, finish
				}
			}
		}
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
	++ltft[0].strokes;
	++ltft[1].strokes;
}

// FUEL_INJECT
#endif
