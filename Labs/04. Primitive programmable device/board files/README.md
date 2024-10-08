# Проверка работы CYBERcobra на ПЛИС

После того, как вы проверили на моделировании дизайн, вам необходимо проверить его работу на прототипе в ПЛИС.

Инструкция по реализации прототипа описана [здесь](../../../Vivado%20Basics/07.%20Program%20and%20debug.md).

На _рис. 1_ представлена схема прототипа в ПЛИС.

![../../../.pic/Labs/board%20files/nexys_cobra_structure.drawio.svg](../../../.pic/Labs/board%20files/nexys_cobra_structure.drawio.svg)

_Рисунок 1. Структурная схема модуля `nexys_CYBERcobra`._

Прототип позволяет потактово исполнять программу, прошитую в память инструкций. Также прототип отображает операцию исполняемую в данный момент.

> [!NOTE]
> Объект модуля `instr_mem` в модуле `CYBERcobra` **должен** называться `imem`. Т.е. строка создания сущности модуля должна выглядеть следующим образом: `instr_mem  imem(...)`.

## Описание используемой периферии

-   ### Переключатели.

    Значение с переключателей `SW[15:0]` подаются напрямую на порт `sw_i` модуля дизайна.

-   ### Кнопки

    -   `BTND` — при нажатии создает тактовый импульс, поступающий на порт тактирования `clk_i` модуля дизайна.
    -   `CPU_RESET` — соединен со входом `rst_i` модуля дизайна. Поскольку в модуле `CYBERcobra` используется синхронный сброс (то есть сигнал сброса учитывается только во время восходящего фронта тактового сигнала), то для сброса модуля `CYBERcobra` и вложенных в него модулей необходимо при зажатой кнопке сброса еще нажать кнопку тактирования.

-   ### Светодиоды

    Светодиоды `LED[15:0]` отображают младшие 16 бит значения, выставленного в данный момент на порте `out_o` модуля дизайна.

-   ### Семисегментные индикаторы

    Семисегментные индикаторы разбиты на 3 блока (см. _рис. 1_):

    -   `out` — отображают младшие 8 бит значения, выставленного в данный момент на порте `out_o` модуля дизайна, в виде шестнадцатеричного числа.
    -   `PC` — отображают в виде шестнадцатеричного числа младшие 8 бит программного счетчика, который подается на вход `addr_i` модуля памяти инструкций.
    -   `operation` — отображают [операцию](#операции-отображаемые-прототипом), исполняемую процессором на текущем такте.

## Операции, отображаемые прототипом

Соответствие типа инструкции отображаемой операции:

1.  Вычислительные — соответствует опкодам вычислительных операций АЛУ.
1.  Инструкция загрузки константы — `LI` (от **l**oad **i**mmediate).
1.  Инструкция загрузки из внешних устройств — `IN` (от **in**put).
1.  Безусловный переход — `JUMP`.
1.  Инструкций условного перехода — соответствует опкодам операций сравнения АЛУ.

Во время исполнения вычислительных инструкций и инструкций условного перехода могут встретиться нелегальные операции (отображается как `ILL`, от **ill**egal). Операция считается нелегальной в следующих случаях:

-   Если в поле инструкции, отвечающем за операция АЛУ, указана битовая последовательность, не входящая в диапазон допустимых значений.
-   Если инструкция является вычислительной, но в поле инструкции, отвечающем за операция АЛУ, указана битовая последовательность, соответствующая операции, вычисляющей флаг. И обратный случай.

Инструкция `0 0 11 xxxxxxxxxxxxxxxxxxxxxxxxxxxx` отображается как `NOP` (от **n**o **op**eration).

Соответствие операции ее отображению на семисегментных индикаторах представлено на _рис. 2_:

!['../../../.pic/Labs/board%20files/nexys_cobra_operations.drawio.svg'](../../../.pic/Labs/board%20files/nexys_cobra_operations.drawio.svg)

_Рисунок 2. Соответствие операции ее отображению на семисегментных индикаторах._


## Демонстрационная программа

В качестве демонстрационной программы, предлагается использовать [program.mem](../program.mem). Описание ее работы можно прочитать в разделе [#финальный обзор](../README.md#финальный-обзор).
