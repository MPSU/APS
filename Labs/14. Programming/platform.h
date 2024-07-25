/* -----------------------------------------------------------------------------
* Project Name   : Architectures of Processor Systems (APS) lab work
* Organization   : National Research University of Electronic Technology (MIET)
* Department     : Institute of Microdevices and Control Systems
* Author(s)      : Andrei Solodovnikov
* Email(s)       : hepoh@org.miet.ru

See https://github.com/MPSU/APS/blob/master/LICENSE file for licensing details.
* ------------------------------------------------------------------------------
*/
#pragma once
#include <stdint.h>

#ifdef __cplusplus
#define CAST(type, addr) reinterpret_cast<type>(addr)
#else
#define CAST(type, addr) (type)(addr)
#endif

/*
  При включенных уровнях оптимизации, компилятор может следить за тем,
  присваиваем ли мы что-то переменной, и если нет — считать что это не переменная
  а константа и выкинуть её из программы.
  Ключевое слово volatile сообщает компилятору, что значение данного объекта
  может быть изменено извне. Например (как это происходит в нашем случае),
  значение может меняться контроллером периферийного устройства.
*/

struct SW_HANDLE
{
  volatile const uint32_t value;
};
struct SW_HANDLE *const sw_ptr = CAST(struct SW_HANDLE *const, 0x01000000);

struct LED_HANDLE
{
  volatile       uint32_t value;
  volatile       uint32_t mode;
  volatile const uint32_t __unused__[7];
  volatile       uint32_t rst;
};
struct LED_HANDLE *const led_ptr = CAST(struct LED_HANDLE *const, 0x02000000);

struct PS2_HANDLE
{
  volatile const uint32_t scan_code;
  volatile const uint32_t unread_data;
  volatile const uint32_t __unused__[7];
  volatile       uint32_t rst;
};
struct PS2_HANDLE *const ps2_ptr = CAST(struct PS2_HANDLE *const, 0x03000000);

struct HEX_HANDLE
{
  volatile uint32_t hex0;
  volatile uint32_t hex1;
  volatile uint32_t hex2;
  volatile uint32_t hex3;
  volatile uint32_t hex4;
  volatile uint32_t hex5;
  volatile uint32_t hex6;
  volatile uint32_t hex7;
  volatile uint32_t bitmask;
  volatile uint32_t rst;
};
struct HEX_HANDLE *const hex_ptr = CAST(struct HEX_HANDLE *const, 0x04000000);

struct RX_HANDLE
{
  volatile const uint32_t data;
  volatile const uint32_t unread_data;
  volatile const uint32_t busy;
  volatile       uint32_t baudrate;
  volatile       uint32_t parity_bit;
  volatile       uint32_t stop_bit;
  volatile const uint32_t __unused__[3];
  volatile       uint32_t rst;
};
struct RX_HANDLE *const rx_ptr = CAST(struct RX_HANDLE *const, 0x05000000);

struct TX_HANDLE
{
  volatile       uint32_t data;
  volatile const uint32_t __unused1__[1];
  volatile const uint32_t busy;
  volatile       uint32_t baudrate;
  volatile       uint32_t parity_bit;
  volatile       uint32_t stop_bit;
  volatile const uint32_t __unused2__[3];
  volatile       uint32_t rst;
};
struct TX_HANDLE *const tx_ptr = CAST(struct TX_HANDLE *const, 0x06000000);

struct VGA_HANDLE
{
  volatile uint8_t *const char_map;
  volatile uint8_t *const color_map;
  volatile uint8_t *const tiff_map;
};
struct VGA_HANDLE vga = {CAST(uint8_t *const, 0x07000000), CAST(uint8_t *const, 0x07001000), CAST(uint8_t *const, 0x07002000)};

struct TIMER_HANDLE
{
  volatile const uint32_t system_counter_low_bits;
  volatile const uint32_t system_counter_high_bits;
  volatile       uint32_t delay_low_bits;
  volatile       uint32_t delay_high_bits;
  volatile       uint32_t mode;
  volatile       uint32_t repeat_counter;
  volatile const uint32_t __unused2__[3];
  volatile       uint32_t rst;
};
struct TIMER_HANDLE *const timer_ptr = CAST(struct TIMER_HANDLE *const, 0x08000000);

struct SUPER_COLLIDER_HANDLE
{
  volatile const uint32_t         ready;
  volatile       uint32_t         start;
  volatile const uint32_t         status;
  volatile       uint32_t         emergency_switch;
  volatile        uint8_t *const  mem;
};
struct SUPER_COLLIDER_HANDLE *const collider_ptr = CAST(struct SUPER_COLLIDER_HANDLE *const, 0xFF000000);
struct SUPER_COLLIDER_HANDLE        collider_obj = {0, 0, 0, 0, CAST(uint8_t *const, 0xFF000100)};
