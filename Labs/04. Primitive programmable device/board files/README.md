# Проверка работы CYBERcobra на ПЛИС

После того, как вы проверили на моделировании дизайн, вам необходимо проверить его работу на прототипе в ПЛИС.

Инструкция по реализации прототипа описана [здесь](../../../Vivado%20Basics/How%20to%20program%20an%20fpga%20board.md).

На _рис. 1_ представлена схема прототипа в ПЛИС.

![../../../.pic/Labs/board%20files/nexys_cobra_structure.drawio.svg](../../../.pic/Labs/board%20files/nexys_cobra_structure.drawio.svg)

_Рисунок 1. Структурная схема модуля `nexys_CYBERcobra`._

Прототип позволяет потактово исполнять программу прошитую в память инструкций, а также отображает операцию исполняемую в данный момент.

> [!NOTE]
> Объекта модуля `instr_mem` в модуле `CYBERcobra` **должен** называться `instr_mem` (т.е. строка объявления модуля выглядит: `instr_mem  instr_mem(...)`.

## Описание используемой периферии

-   ### Переключатели.

    Значение с переключателей `SW[15:0]` подаются напрямую на порт `sw_i` модуля дизайна.

-   ### Кнопки

    -   `BTND` — при нажатии создает тактовый импульс, поступающий на порт тактирования `clk_i` модуля дизайна.
    -   `CPU_RESET` — соединен со входом `rst_i` модуля дизайна.

-   ### Светодиоды

    Светодиоды `LED[14:0]` отображают нижние 16 бит значения, выставленного в данный момент на порте `out_o` модуля дизайна.

-   ### Семисегментные индикаторы

    Пронумеруем индикаторы от `0` до `7`, индикатор `7` является крайним левым. Семисегментные индикаторы разбиты на 3 блока:

    -   `[7:6]` — дублируют нижние 8 бит значения, выставленного в данный момент на порте `out_o` модуля дизайна, в виде шестнадцатеричного числа.
    -   `[5:4]` — отображают нижние 8 бит значения, выставленного в данный момент на порте `addr_i` модуля `instr_mem`. Значение этого сигнала соответствует значению программного счетчика в данный момент, в виде шестнадцатеричного числа.
    -   `[3:0]` — отображают [операцию](#операции-отображаемые-прототипом), которую CYBERcobra исполняется в данный момент, в виде набора букв английского алфавита, а также символа пробела. Прототип определяет операцию путем декодирования значения, выставленного в данный момент на порте `read_data_o` модуля `instr_mem`.

## Операции, отображаемые прототипом

Алфавит представлен ниже:

-   A — <img src='../../../.pic/Labs/board%20files/semseg_alphabet/A.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/A.svg' width='16'>
-   b — <img src='../../../.pic/Labs/board%20files/semseg_alphabet/b.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/b.svg' width='16'>
-   C — <img src='../../../.pic/Labs/board%20files/semseg_alphabet/C.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/C.svg' width='16'>
-   d — <img src='../../../.pic/Labs/board%20files/semseg_alphabet/d.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/d.svg' width='16'>
-   E — <img src='../../../.pic/Labs/board%20files/semseg_alphabet/E.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/E.svg' width='16'>
-   F — <img src='../../../.pic/Labs/board%20files/semseg_alphabet/F.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/F.svg' width='16'>
-   G — <img src='../../../.pic/Labs/board%20files/semseg_alphabet/G.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/G.svg' width='16'>
-   L — <img src='../../../.pic/Labs/board%20files/semseg_alphabet/L.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/L.svg' width='16'>
-   n — <img src='../../../.pic/Labs/board%20files/semseg_alphabet/n.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/n.svg' width='16'>
-   o — <img src='../../../.pic/Labs/board%20files/semseg_alphabet/o.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/o.svg' width='16'>
-   r — <img src='../../../.pic/Labs/board%20files/semseg_alphabet/r.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/r.svg' width='16'>
-   S — <img src='../../../.pic/Labs/board%20files/semseg_alphabet/S.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/S.svg' width='16'>
-   t — <img src='../../../.pic/Labs/board%20files/semseg_alphabet/t.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/t.svg' width='16'>
-   u — <img src='../../../.pic/Labs/board%20files/semseg_alphabet/u.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/u.svg' width='16'>
-   X — <img src='../../../.pic/Labs/board%20files/semseg_alphabet/X.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/X.svg' width='16'>
-   P — <img src='../../../.pic/Labs/board%20files/semseg_alphabet/P.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/P.svg' width='16'>
-   J — <img src='../../../.pic/Labs/board%20files/semseg_alphabet/J.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/J.svg' width='16'>
-   q — <img src='../../../.pic/Labs/board%20files/semseg_alphabet/q.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/q.svg' width='16'>
-   i — <img src='../../../.pic/Labs/board%20files/semseg_alphabet/i.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/i.svg' width='16'>
-   m — <img src='../../../.pic/Labs/board%20files/semseg_alphabet/m.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/m.svg' width='16'>
-   space — <img src='../../../.pic/Labs/board%20files/semseg_alphabet/space.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/space.svg' width='16'>

Соответствие типа инструкции отображаемой операции:

1.  Вычислительные — отображается вычислительная операция, исполняемая на alu (например, <img src='../../../.pic/Labs/board%20files/semseg_alphabet/A.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/A.svg' width='16'><img src='../../../.pic/Labs/board%20files/semseg_alphabet/d.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/d.svg' width='16'><img src='../../../.pic/Labs/board%20files/semseg_alphabet/d.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/d.svg' width='16'><img src='../../../.pic/Labs/board%20files/semseg_alphabet/space.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/space.svg' width='16'>).
1.  Инструкция загрузки константы  — <img src='../../../.pic/Labs/board%20files/semseg_alphabet/L.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/L.svg' width='16'><img src='../../../.pic/Labs/board%20files/semseg_alphabet/i.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/i.svg' width='16'><img src='../../../.pic/Labs/board%20files/semseg_alphabet/space.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/space.svg' width='16'>
1.  Инструкция загрузки из внешних устройств — <img src='../../../.pic/Labs/board%20files/semseg_alphabet/i.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/i.svg' width='16'><img src='../../../.pic/Labs/board%20files/semseg_alphabet/n.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/n.svg' width='16'><img src='../../../.pic/Labs/board%20files/semseg_alphabet/space.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/space.svg' width='16'><img src='../../../.pic/Labs/board%20files/semseg_alphabet/space.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/space.svg' width='16'>
1.  Безусловный переход — <img src='../../../.pic/Labs/board%20files/semseg_alphabet/J.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/J.svg' width='16'><img src='../../../.pic/Labs/board%20files/semseg_alphabet/u.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/u.svg' width='16'><img src='../../../.pic/Labs/board%20files/semseg_alphabet/m.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/m.svg' width='16'><img src='../../../.pic/Labs/board%20files/semseg_alphabet/P.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/P.svg' width='16'>
1.  Инструкций условного перехода — отображается операция вычисления флага, исполняемая на alu (например, <img src='../../../.pic/Labs/board%20files/semseg_alphabet/L.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/L.svg' width='16'><img src='../../../.pic/Labs/board%20files/semseg_alphabet/E.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/E.svg' width='16'><img src='../../../.pic/Labs/board%20files/semseg_alphabet/S.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/S.svg' width='16'><img src='../../../.pic/Labs/board%20files/semseg_alphabet/space.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/space.svg' width='16'>).

Во время исполнения вычислительных инструкций и инструкций условного перехода могут встретиться нелегальные операции (отображается как <img src='../../../.pic/Labs/board%20files/semseg_alphabet/i.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/i.svg' width='16'><img src='../../../.pic/Labs/board%20files/semseg_alphabet/L.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/L.svg' width='16'><img src='../../../.pic/Labs/board%20files/semseg_alphabet/L.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/L.svg' width='16'><img src='../../../.pic/Labs/board%20files/semseg_alphabet/space.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/space.svg' width='16'>, illegal):

-   Если в поле инструкции, отвечающем за операция АЛУ, указана битовая последовательность, не входящая в диапазон допустимых значений.
-   Если инструкций является вычислительной, но в поле инструкции, отвечающем за операция АЛУ, указана битовая последовательность, соответствующая инструкции условного перехода. И обратный случай.

Инструкция `0 0 11 xxxxxxxxxxxxxxxxxxxxxxxxxxxx` отображается как <img src='../../../.pic/Labs/board%20files/semseg_alphabet/n.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/n.svg' width='16'><img src='../../../.pic/Labs/board%20files/semseg_alphabet/o.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/o.svg' width='16'><img src='../../../.pic/Labs/board%20files/semseg_alphabet/P.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/P.svg' width='16'><img src='../../../.pic/Labs/board%20files/semseg_alphabet/space.svg' alt= '../../../.pic/Labs/board%20files/semseg_alphabet/space.svg' width='16'> (no operation).

## Демонстрационная программа

Демонстрационная программа, написанная на языке ассемблера, представлена ниже.

```
0x00: li x1, 32
0x04: add x0, x1, x0
0x08: add x2, x2, x3
0x0C: sub x2, x2, x3
0x10: xor x2, x2, x3
0x14: or x2, x2, x3
0x18: and x2, x2, x3
0x1C: sra x2, x2, x3
0x20: srl x2, x2, x3
0x24: sll x2, x2, x3
0x28: lts x0, x1, 10
0x2C: ltu x0, x1, 10
0x30: ges x1, x0, 10
0x34: geu x1, x0, 10
0x38: eq x0, x0, 10
0x3C: ne x1, x0, 10
0x40: lts x1, x2, x3
0x44: ltu x1, x2, x3
0x48: in x1
0x4C: jump -19
0x50: jump -9
0x54: jump -9
0x58: jump -9
0x5C: jump -9
0x60: jump -9
0x64: jump -9
```

Программа содержит все инструкции из ISA, кроме нелегальных и `no operation`. Вначале каждой строки указан адрес инструкции в `instr_mem` в шестнадцатеричном формате. После выполнения всех инструкций осуществляется безусловный переход в самое начало программы, зацикливая программу таким образом. Версия этой программы, транслированная в машинные коды, находится в файле [demo.mem](./demo.mem).

<!-- Как демонстрация, на _рис. 2_ изображено состояние прототипа на ПЛИС во время исполнения инструкции по адресу `0x04`. -->
