# Проверка работы регистрового файла на ПЛИС

После того, как вы проверили на моделировании регистровый файл, вам необходимо проверить его работу на прототипе в ПЛИС.

Инструкция по реализации прототипа описана [здесь](../../../Vivado%20Basics/07.%20Program%20and%20debug.md).

На _рис. 1_ представлена схема прототипа в ПЛИС.

![../../../.pic/Labs/board%20files/nexys_rf_riscv_structure.drawio.svg](../../../.pic/Labs/board%20files/nexys_rf_riscv_structure.drawio.svg)

_Рисунок 1. Структурная схема модуля `nexys_rf_riscv`._

## Описание используемой периферии

Периферия показана на _рис. 2_.

![../../../.pic/Labs/board%20files/nexys_rf_riscv_control.drawio.svg](../../../.pic/Labs/board%20files/nexys_rf_riscv_control.drawio.svg)

_Рисунок 2. Периферия, доступная прототипу._

-   ### Переключатели и кнопки.

    Для работы с регистровым файлом необходимо выставлять сигналы адресов и данных.
    У платы недостаточно переключателей для такого количества входов регистрового файла, поэтому адреса и данные задаются одним источником ввода:

    1.  Ввод **адресов** (`read_addr1_i`/`read_addr2_i`/`write_addr_i`) регистрового файла осуществляется через переключатели `SW[14:0]`. Соответствие следующее:

        -   `SW[ 4: 0]` — `write_addr_i`
        -   `SW[ 9: 5]` — `read_addr2_i`
        -   `SW[14:10]` — `read_addr1_i`

        Для того чтобы выставить введенные адреса на входные порты регистрового файла, необходимо нажать кнопку `BTND` (`addr_en` на _рис. 2_). Таким образом, происходит запоминание адресов в элемент памяти.
    1.  Ввод **данных** (`write_data_i`) регистрового файла осуществляется через переключатели `SW[15:0]`. Таким образом, можно выставить только младшие 16 бит данных. Для записи введенных данных по адресу `write_addr_i` используется кнопка `BTNR` (`we` на _рис. 2_).
-   ### Светодиоды

    Светодиоды `LED[14:0]` отображают адреса (`read_addr1_i`/`read_addr2_i`/`write_addr_i`), которые выставлены в данный момент на порты регистрового файла:

    -   `LED[ 4: 0]` — `write_addr_i`
    -   `LED[ 9: 5]` — `read_addr2_i`
    -   `LED[14:10]` — `read_addr1_i`

-   ### Семисегментные индикаторы

    На левом блоке семисегментных индикаторов (индикаторы 7-4) отображется значение младших 16-ти бит порта `read_data1_o`, а на правом блоке семисегментных индикаторов (индикаторы 3-0) отображается значение младших 16-ти бит порта `read_data2_o`.

    Числа отображаются в **шестнадцатеричном** формате.

## Выполнение операций с регистровым файлом на прототипе

Доступные операции: запись, чтение.

-   ### Запись

    Рассмотрим последовательность действий, которые надо осуществить для записи в регистровый файл, на примере.

    1.  Запишем значение `0x1234` в регистр `5`.

        1.  Сразу после прошивки, как видно по негорящим светодиодам, на портах регистрового файла выставлены нулевые адреса. Нам нужно изменить адрес записи, поэтому выставим на переключателях значение `5` и нажмем кнопку `BTND` (см. _рис. 3_).

            ![../../../.pic/Labs/board%20files/nexys_rf_riscv_write_addr_5.drawio.svg](../../../.pic/Labs/board%20files/nexys_rf_riscv_write_addr_5.drawio.svg)

            _Рисунок 3. Выставление адреса `5` на порт `write_addr_i` регистрового файла._

            Обратите внимание: на светодиодах сразу после нажатия кнопки отображается адрес `5`.
        1.  Чтобы записать данные в указанный (пятый) регистр, выставим на переключателях значение `0x1234` и нажмем кнопку `BTNR` (см. _рис. 4_).

            ![../../../.pic/Labs/board%20files/nexys_rf_riscv_write_data_1234.drawio.svg](../../../.pic/Labs/board%20files/nexys_rf_riscv_write_data_1234.drawio.svg)

            _Рисунок 4. Запись `0x1234` в регистр `5`._

    1.  Запишем значение `0x5678` в регистр `6`.

        1.  Выставим на блок переключателей, отвечающих за порт записи, значение `6` и нажмем кнопку `BTND` (см. _рис. 5_).

            ![../../../.pic/Labs/board%20files/nexys_rf_riscv_write_addr_6.drawio.svg](../../../.pic/Labs/board%20files/nexys_rf_riscv_write_addr_6.drawio.svg)

            _Рисунок 5. Выставление адреса `6` на порт `write_addr_i` регистрового файла._

            Обратите внимание: на светодиодах сразу после нажатия кнопки отображается адрес `6`.
        1.  Чтобы записать данные в указанный (шестой) регистр, выставим на переключателях значение `0x5678` и нажмем кнопку `BTNR` (см. _рис. 6_).

            ![../../../.pic/Labs/board%20files/nexys_rf_riscv_write_data_5678.drawio.svg](../../../.pic/Labs/board%20files/nexys_rf_riscv_write_data_5678.drawio.svg)

            _Рисунок 6. Запись `0x5678` в регистр `6`._

-   ### Чтение

    Рассмотрим последовательность действий, которые надо осуществить для чтения из регистрового файла, на примере. Прочитаем из регистров `5` и `6` заранее записанные значения `0x1234` и `0x5678` соответственно и выведем его на оба блока семисегментных индикаторов 7-0 и 3-0.

    Выставим значение `5` и `6` на блоки переключателей `ra1` и `ra2` (см. _рис. 2_) соответственно, и нажмем кнопку `BTND`, чтобы обновить адрес значением с переключателей (см. _рис. 7_).

    ![../../../.pic/Labs/board%20files/nexys_rf_riscv_read.drawio.svg](../../../.pic/Labs/board%20files/nexys_rf_riscv_read.drawio.svg)

    _Рисунок 7. Чтение из регистров `5` и `6`._

    Обратите внимание на то, что для чтения достаточно выставить нужный адрес на порт регистрового файла, и содержимое регистра оказывается считанным.

> [!NOTE]
> Кнопка сброса `CPU_RESETN` не сбрасывает содержимое регистрового файла, т.к. сигнал сброса не заведен в модуль регистрового файла, а модуль `nexys_rf_riscv` самостоятельно его не сбрасывает. Для сброса можно осуществить перепрошивку ПЛИС.

Попробуйте записать информацию в нулевой регистр, затем по другим адресам. После чего считайте записанную информацию и убедитесь, что она соответствует той, которую вы записывали (с учетом особенностей регистрового файла RISC-V).
