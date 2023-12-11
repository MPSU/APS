#pragma once
#include <stdint.h>

#ifdef __cplusplus
#define CAST(type, addr) reinterpret_cast<type>(addr)
#else
#define CAST(type, addr) (type) (addr)
#endif

struct SW_HANDLE
{
  const uint32_t value;
};

struct LED_HANDLE
{
        uint32_t value;
        uint32_t mode;
  const uint32_t __unused__[7];
        uint32_t rst;
};

struct PS2_HANDLE
{
  const uint32_t scan_code;
  const uint32_t unread_data;
  const uint32_t __unused__[7];
        uint32_t rst;
};

struct HEX_HANDLE
{
        uint32_t hex0;
        uint32_t hex1;
        uint32_t hex2;
        uint32_t hex3;
        uint32_t hex4;
        uint32_t hex5;
        uint32_t hex6;
        uint32_t hex7;
        uint32_t bitmask;
        uint32_t rst;
};

struct RX_HANDLE
{
  const uint32_t data;
  const uint32_t unread_data;
  const uint32_t busy;
        uint32_t baudrate;
        uint32_t parity_bit;
        uint32_t stop_bit;
  const uint32_t __unused__[3];
        uint32_t rst;
};

struct TX_HANDLE
{
        uint32_t data;
  const uint32_t __unused1__[1];
  const uint32_t busy;
        uint32_t baudrate;
        uint32_t parity_bit;
        uint32_t stop_bit;
  const uint32_t __unused2__[3];
        uint32_t rst;
};

struct VGA_HANDLE
{
        uint32_t *const char_map;
        uint32_t *const color_map;
        uint32_t *const tiff_map;
};

struct SUPER_COLLIDER_HANDLE
{
  const uint32_t ready;
        uint32_t start;
  const uint32_t status;
        uint32_t emergency_switch;
};
