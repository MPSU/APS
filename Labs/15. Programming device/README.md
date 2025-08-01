# Лабораторная работа №15 "Программатор"

Чтобы выпустить микроконтроллер в "дикую природу", то есть, чтобы его можно было использовать не в лабораторных условиях, а независимо от всего этого дополнительного оборудования, необходимо предусмотреть механизм замены исполняемой программы.

## Цель

Реализация программатора — части микроконтроллера, обеспечивающего получение исполняемой программы из внешних, по отношению к системе, устройств.

## Ход работы

1. Познакомиться с информацией о программаторах и загрузчиках ([#теория](#теория))
2. Изучить информацию о конечных автоматах и способах их реализации ([#практика](#практика))
3. Описать перезаписываемую память инструкций ([#память инструкций](#перезаписываемая-память-инструкций))
4. Описать и проверить модуль программатора ([#программатор](#программатор))
5. Интегрировать программатор в процессорную систему и проверить её ([#интеграция](#интеграция-программатора-в-processor_system))
6. Проверить работу системы в ПЛИС с помощью предоставленного скрипта, инициализирующего память системы ([#проверка](#%D0%BF%D1%80%D0%B8%D0%BC%D0%B5%D1%80-%D0%B7%D0%B0%D0%B3%D1%80%D1%83%D0%B7%D0%BA%D0%B8-%D0%BF%D1%80%D0%BE%D0%B3%D1%80%D0%B0%D0%BC%D0%BC%D1%8B))

## Теория

До этого момента исполняемая процессором программа попадала в память инструкций через магический вызов `$readmemh`. Однако, реальные микроконтроллеры не обладают такими возможностями. Программа из внешнего мира попадает в них посредством так называемого **программатора** — устройства, обеспечивающего запись программы в память микроконтроллера. Программатор записывает данные в постоянное запоминающее устройство (ПЗУ). Для того, чтобы программа попала из ПЗУ в память инструкций (в ОЗУ), после запуска микроконтроллера сперва начинает исполняться **загрузчик** (**bootloader**) — небольшая программа, "вшитая" в память микроконтроллера на этапе изготовления. Загрузчик отвечает за первичную инициализацию различных регистров и подготовку микроконтроллера к выполнению основной программы, включая её перенос из ПЗУ в память инструкций.

Со временем появилось несколько уровней загрузчиков: сперва запускается **первичный загрузчик** (**first stage bootloader**, **fsbl**), после которого запускается **вторичный загрузчик** (часто в роли вторичного загрузчика исполняется программа под названием **u-boot**). Такая иерархия загрузчиков может потребоваться, например, в случае загрузки операционной системы (которая хранится в файловой системе). Код для работы с файловой системой может попросту не уместиться в первичный загрузчик. В этом случае, целью первичного загрузчика является лишь загрузить вторичный загрузчик, который в свою очередь уже будет способен взаимодействовать с файловой системой и загрузить операционную систему.

Кроме того, код вторичного загрузчика может быть изменен, поскольку программируется вместе с основной программой. Первичный же загрузчик не всегда может быть изменен.

В рамках данной лабораторной работы мы немного упростим процесс передачи программы: вместо записи в ПЗУ, программатор будет записывать её сразу в память инструкций, минуя загрузчик.

## Практика

### Конечные автоматы (Finite-State Machines, FSM)

Программатор будет представлен в виде модуля с [конечным автоматом](https://en.wikipedia.org/wiki/Finite-state_machine). Конечный автомат представляет собой устройство, состоящее из:

- элемента памяти (так называемого **регистра состояния**);
- логики, обеспечивающей изменение значения **регистра состояния** (логики перехода между состояниями) в зависимости от его текущего состояния и входных сигналов;
- логики, отвечающей за выходы конечного автомата.

Обычно, конечные автоматы описываются в виде направленного графа переходов между состояниями, где вершины графа — это состояния конечного автомата, а рёбра (дуги) — условия перехода из одного состояния в другое.

Простейшим примером конечного автомата может быть турникет. Когда в приёмник турникета опускается подходящий жетон, тот разблокирует вращающуюся треногу. После попытки поворота треноги, та блокируется до следующего жетона.

Иными словами, у турникета есть:

- два состояния
  - заблокирован (`locked`)
  - разблокирован(`unlocked`)
- два входа (события)
  - жетон принят (`coin`)
  - попытка поворота треноги (`push`)
- один выход
  - блокировка треноги

Для описания двух состояний нам будет достаточно однобитного регистра. Для взаимодействия с регистром, нам потребуются также сигнал синхронизации и сброса.

Опишем данный автомат в виде графа переходов:

![../../.pic/Labs/lab_15_programming_device/fig_01.svg](../../.pic/Labs/lab_15_programming_device/fig_01.svg)

_Рисунок 1. Граф переходов конечного автомата для турникета[[1]](https://en.wikipedia.org/wiki/Finite-state_machine)._

Черной точкой со стрелкой в вершину `Locked` обозначен сигнал сброса. Иными словами, при сбросе турникет всегда переходит в заблокированное состояние.

Как мы видим, повторное опускание жетона в разблокированном состоянии приводит к сохранению этого состояния (но турникет не запоминает, что было опущено 2 жетона, и после первого же прохода станет заблокирован). В случае попытки поворота треноги в заблокированном состоянии, автомат так и останется в заблокированном состоянии.

Так же необходимо оговорить приоритет переходов: в первую очередь проверяется попытка поворота треноги, в случае если такой попытки не было, проверяется опускание монетки. Такой приоритет можно было бы указать и на графе, показав на рёбрах что переход в состояние unlocked возможен только при отсутствии сигнала `push`.

### Реализация конечных автоматов в SystemVerilog

Глядя на описание составляющих конечного автомата, вы могли задаться вопросом: чем автомат отличается от последовательностной логики, ведь она состоит из тех же компонент. Ответом будет: ничем. Конечные автоматы являются математической абстракцией над функцией последовательностной логики[[2]](https://www.allaboutcircuits.com/textbook/digital/chpt-11/finite-state-machines/). Иными словами — конечный автомат, это просто другой способ представления последовательностной логики, а значит вы уже умеете их реализовывать.

Для реализации регистра состояния конечного автомата будет удобно воспользоваться специальным типом языка **SystemVerilog**, который называется `enum` (**перечисление**).

Перечисления позволяют объявить объединенный набор именованных констант. В дальнейшем, объявленные имена можно использовать вместо перечисленных значений, им соответствующих, что повышает читаемость кода. Если не указано иного, первому имени присваивается значение `0`, каждое последующее увеличивается на `1` относительно предыдущего значения.

```Verilog
module turnstile_fsm(
  input  logic clk,
  input  logic rst,
  input  logic push,
  input  logic coin,
  output logic is_locked
);

  enum logic {LOCKED=1, UNLOCKED=0} state;

  assign is_locked = state == LOCKED;

  always_ff @(posedge clk) begin
    if(rst) begin
      state <= LOCKED;
    end
    else begin
      if(push) begin
        state <= LOCKED;
      end
      else if (coin) begin
        state <= UNLOCKED;
      end
      else begin
        state <= state;
      end
    end
  end
endmodule
```

_Листинг 1. Пример реализации конечного автомата для турникета._

Кроме того, при должной поддержке со стороны инструментов моделирования, значения объектов перечислений могут выводиться на временную диаграмму в виде перечисленных имен:

![../../.pic/Labs/lab_15_programming_device/fig_02.png](../../.pic/Labs/lab_15_programming_device/fig_02.png)

_Рисунок 2. Вывод значений объекта `enum` на временную диаграмму._

Для описания регистра состояния часто используют отдельный комбинационный сигнал, который подаётся непосредственно на его вход (часто именуемый как `next_state`). Приведённый выше автомат турникета слишком простой, чтобы показать преимущества такого подхода. Предположим, что в момент перехода из состояния `locked` в состояние `unlocked` мы хотим, чтобы загоралась и сразу гасла зелёная лампочка. Без сигнала `next_state` подобный модуль можно было бы описать как:

```Verilog
module turnstile_fsm(
  input  logic clk,
  input  logic rst,
  input  logic push,
  input  logic coin,
  output logic is_locked,
  output logic green_light
);

  enum logic {LOCKED=1, UNLOCKED=0} state;

  assign is_locked = state == LOCKED;

  // (!push) && coin — условие перехода в состояние UNLOCKED
  assign green_light = (state == LOCKED) && (!push) && coin;

  always_ff @(posedge clk) begin
    if(rst) begin
      state <= LOCKED;
    end
    else begin
      if(push) begin
        state <= LOCKED;
      end
      else if (coin) begin
        state <= UNLOCKED;
      end
      else begin
        state <= state;
      end
    end
  end
endmodule
```

_Листинг 2. Пример реализации конечного автомата для усложнённого турникета._

Используя сигнал `next_state`, автомат мог бы быть переписан следующим образом:

```Verilog
module turnstile_fsm(
  input  logic clk,
  input  logic rst,
  input  logic push,
  input  logic coin,
  output logic is_locked,
  output logic green_light
);

  enum logic {LOCKED=1, UNLOCKED=0} state, next_state;

  assign is_locked = state == LOCKED;

  assign green_light = (state == LOCKED) && (next_state == UNLOCKED);

  always_ff @(posedge clk) begin
    if(rst) begin
      state <= LOCKED;
    end
    else begin
      state <= next_state;
    end
  end

  always_comb begin
    if(push) begin
      next_state = LOCKED;
    end
    else if (coin) begin
      next_state = UNLOCKED;
    end
    else begin
      next_state = state;
    end
  end
endmodule
```

_Листинг 3. Пример реализации конечного автомата для усложнённого турникета с использованием сигнала next\_state._

На первый взгляд может показаться, что так даже сложнее. Во-первых, появился дополнительный сигнал. Во-вторых, появился ещё один `always`-блок. Однако представьте на секунду, что условиями перехода будет что-то сложнее, чем 1-битный входной сигнал. И что от этих условий будет зависеть не один выходной сигнал, а множество как выходных сигналов, так и внутренних элементов памяти помимо регистра состояний. В этом случае, сигнал `next_state` позволит избежать дублирования множества условий.

Важно отметить, что объектам типа `enum` можно присваивать только перечисленные константы и объекты того же типа. Иными словами, `state` можно присваивать значения `LOCKED`/`UNLOCKED` и `next_state`, но нельзя, к примеру, присвоить `1'b0`.

## Задание

Для выполнения данной лабораторной работы необходимо:

- описать перезаписываемую память инструкций;
- описать модуль-программатор;
- заменить в `processor_system` память инструкций на новую, и интегрировать программатор.

### Перезаписываемая память инструкций

Поскольку ранее из памяти инструкций можно было только считывать данные, но не записывать их в неё, программатор не сможет записать принятую из внешнего мира программу. Поэтому необходимо добавить в память инструкций порт на запись. Для того, чтобы различать реализации памяти инструкций, данный модуль будет называться `rw_instr_mem`:

```Verilog
module rw_instr_mem
import memory_pkg::INSTR_MEM_SIZE_BYTES;
import memory_pkg::INSTR_MEM_SIZE_WORDS;
(
  input  logic        clk_i,
  input  logic [31:0] read_addr_i,
  output logic [31:0] read_data_o,

  input  logic [31:0] write_addr_i,
  input  logic [31:0] write_data_i,
  input  logic        write_enable_i
);

  logic [31:0] ROM [INSTR_MEM_SIZE_WORDS];

  assign read_data_o = ROM[read_addr_i[$clog2(INSTR_MEM_SIZE_BYTES)-1:2]];

  always_ff @(posedge clk_i) begin
    if(write_enable_i) begin
      ROM[write_addr_i[$clog2(INSTR_MEM_SIZE_BYTES)-1:2]] <= write_data_i;
    end
  end

endmodule
```

_Листинг 4. Модуль rw\_instr\_mem._

### Программатор

Необходимо реализовать модуль программатора, использующий с одной "стороны" `uart` в качестве интерфейса для обмена данными с внешним миром, а с другой — интерфейсы для записи полученных данных в память инструкций и память данных.

#### Описание модуля

В основе работы модуля лежит конечный автомат со следующим графом перехода между состояниями:

![../../.pic/Labs/lab_15_programming_device/fig_03.drawio.svg](../../.pic/Labs/lab_15_programming_device/fig_03.drawio.svg)

_Рисунок 3. Граф перехода между состояниями программатора._

Данный автомат реализует следующий алгоритм:

1. Получение команды ("запись очередного блока" / "программирование завершено"). Данная команда представляет собой адрес записи очередного блока, и в случае, если адрес равен 0xFFFFFFFF, это означает команду "программирование завершено".
   1. В случае получения команды "программирование завершено", модуль завершает свою работу, снимая сигнал сброса с процессора.
   2. В случае получения команды "запись очередного блока" происходит переход к п. 2.
2. Модуль отправляет сообщение о готовности принимать размер очередного блока.
3. Выполняется передача размера очередного блока.
4. Модуль подтверждает получение размера очередного блока и повторяет его значение.
5. Выполняется передача очередного блока, который записывается, начиная с адреса, принятого в п.1.
6. Получив заданное в п.3 количество байт очередного блока, модуль сообщает о завершении записи и переходит к ожиданию очередной команды в п.1.

На графе перехода автомата обозначены следующие условия:

- `send_fin   = (  msg_counter == 0) && !tx_busy` — условие завершения передачи модулем сообщения по `uart_tx`;
- `size_fin   = ( size_counter == 0) && !rx_busy` — условие завершения приема модулем размера будущей посылки;
- `flash_fin  = (flash_counter == 0) && !rx_busy` — условие завершения приема модулем блока записываемых данных;
- `next_round = (flash_addr    !='1) && !rx_busy` — условие записи блока данных через системную шину;

Ниже представлен прототип модуля с частично реализованной логикой:

```Verilog
module bluster
(
  input   logic clk_i,
  input   logic rst_i,

  input   logic rx_i,
  output  logic tx_o,

  output logic [ 31:0] instr_addr_o,
  output logic [ 31:0] instr_wdata_o,
  output logic         instr_we_o,

  output logic [ 31:0] data_addr_o,
  output logic [ 31:0] data_wdata_o,
  output logic         data_we_o,

  output logic core_reset_o
);

import memory_pkg::INSTR_MEM_SIZE_BYTES;
import bluster_pkg::INIT_MSG_SIZE;
import bluster_pkg::FLASH_MSG_SIZE;
import bluster_pkg::ACK_MSG_SIZE;

enum logic [2:0] {
  RCV_NEXT_COMMAND,
  INIT_MSG,
  RCV_SIZE,
  SIZE_ACK,
  FLASH,
  FLASH_ACK,
  FINISH}
state, next_state;

logic rx_busy, rx_valid, tx_busy, tx_valid;
logic [7:0] rx_data, tx_data;

logic [5:0] msg_counter;
logic [31:0] size_counter, flash_counter;
logic [3:0] [7:0] flash_size, flash_addr;

logic send_fin, size_fin, flash_fin, next_round;

assign send_fin   = (msg_counter    ==  0)  && !tx_busy;
assign size_fin   = (size_counter   ==  0)  && !rx_busy;
assign flash_fin  = (flash_counter  ==  0)  && !rx_busy;
assign next_round = (flash_addr     != '1)  && !rx_busy;

logic [7:0] [7:0] flash_size_ascii, flash_addr_ascii;
// Блок generate позволяет создавать структуры модуля цикличным или условным
// образом. В данном случае, при описании непрерывных присваиваний была
// обнаружена закономерность, позволяющая описать четверки присваиваний в более
// общем виде, который был описан в виде цикла.
// Важно понимать, данный цикл лишь автоматизирует описание присваиваний и во
// время синтеза схемы развернется в четыре четверки непрерывных присваиваний.
genvar i;
generate
  for(i=0; i < 4; i=i+1) begin
    // Данная логика преобразовывает сигналы flash_size и flash_addr,
    // которые представляют собой "сырые" двоичные числа в ASCII-символы[1]

    // Разделяем каждый байт flash_size и flash_addr на два ниббла.
    // Ниббл — это 4 бита. Каждый ниббл можно описать 16-битной цифрой.
    // Если ниббл меньше 10 (4'ha), он описывается цифрами 0-9. Чтобы представить
    // его ascii-кодом, необходимо прибавить к нему число 8'h30
    // (ascii-код символа '0').
    // Если ниббл больше либо равен 10, он описывается буквами a-f. Для его
    // представления в виде ascii-кода, необходимо прибавить число 8'h57
    // (это уменьшенный на 10 ascii-код символа 'a' = 8'h61).
    assign flash_size_ascii[i*2]    = flash_size[i][3:0] < 4'ha ? flash_size[i][3:0] + 8'h30 :
                                                                  flash_size[i][3:0] + 8'h57;
    assign flash_size_ascii[i*2+1]  = flash_size[i][7:4] < 4'ha ? flash_size[i][7:4] + 8'h30 :
                                                                  flash_size[i][7:4] + 8'h57;

    assign flash_addr_ascii[i*2]    = flash_addr[i][3:0] < 4'ha ? flash_addr[i][3:0] + 8'h30 :
                                                                  flash_addr[i][3:0] + 8'h57;
    assign flash_addr_ascii[i*2+1]  = flash_addr[i][7:4] < 4'ha ? flash_addr[i][7:4] + 8'h30 :
                                                                  flash_addr[i][7:4] + 8'h57;
  end
endgenerate

logic [INIT_MSG_SIZE-1:0][7:0] init_msg;
// ascii-код строки "ready for flash starting from 0xflash_addr\n"
assign init_msg = { 8'h72, 8'h65, 8'h61, 8'h64, 8'h79, 8'h20, 8'h66, 8'h6F,
                    8'h72, 8'h20, 8'h66, 8'h6C, 8'h61, 8'h73, 8'h68, 8'h20,
                    8'h73, 8'h74, 8'h61, 8'h72, 8'h74, 8'h69, 8'h6E, 8'h67,
                    8'h20, 8'h66, 8'h72, 8'h6F, 8'h6D, 8'h20, 8'h30, 8'h78,
                    flash_addr_ascii, 8'h0a};

logic [FLASH_MSG_SIZE-1:0][7:0] flash_msg;
//ascii-код строки: "finished write 0xflash_size bytes starting from 0xflash_addr\n"
assign flash_msg = {8'h66, 8'h69, 8'h6E, 8'h69, 8'h73, 8'h68, 8'h65, 8'h64,
                    8'h20, 8'h77, 8'h72, 8'h69, 8'h74, 8'h65, 8'h20, 8'h30,
                    8'h78,      flash_size_ascii,      8'h20, 8'h62, 8'h79,
                    8'h74, 8'h65, 8'h73, 8'h20, 8'h73, 8'h74, 8'h61, 8'h72,
                    8'h74, 8'h69, 8'h6E, 8'h67, 8'h20, 8'h66, 8'h72, 8'h6F,
                    8'h6D, 8'h20, 8'h30, 8'h78,     flash_addr_ascii,
                    8'h0a};

uart_rx rx(
  .clk_i      (clk_i      ),
  .rst_i      (rst_i      ),
  .rx_i       (rx_i       ),
  .busy_o     (rx_busy    ),
  .baudrate_i (17'd115200 ),
  .parity_en_i(1'b1       ),
  .stopbit_i  (2'b1       ),
  .rx_data_o  (rx_data    ),
  .rx_valid_o (rx_valid   )
);

uart_tx tx(
  .clk_i      (clk_i      ),
  .rst_i      (rst_i      ),
  .tx_o       (tx_o       ),
  .busy_o     (tx_busy    ),
  .baudrate_i (17'd115200 ),
  .parity_en_i(1'b1       ),
  .stopbit_i  (2'b1       ),
  .tx_data_i  (tx_data    ),
  .tx_valid_i (tx_valid   )
);

endmodule
```

_Листинг 5. Готовая часть программатора._

Здесь уже объявлены:

- `enum`-сигналы `state` и `next_state`;
- сигналы, `send_fin`, `size_fin`, `flash_fin`, `next_round`, используемые в качестве условий переходов между состояниями;
- счетчики `msg_counter`, `size_counter`, `flash_counter`, необходимые для реализации условий переходов;
- сигналы, необходимые для подключения модулей `uart_rx` и `uart_tx`:
  - `rx_busy`,
  - `rx_valid`,
  - `tx_busy`,
  - `tx_valid`,
  - `rx_data`,
  - `tx_data`;
- модули `uart_rx`, `uart_tx`;
- сигналы `init_msg`, `flash_msg`, хранящие ascii-код ответов программатора, а также логику и сигналы, необходимые для реализации этих ответов:
  - `flash_size`,
  - `flash_addr`,
  - `flash_size_ascii`,
  - `flash_addr_ascii`.

#### Реализация модуля программатора

Для реализации данного модуля, необходимо реализовать все объявленные выше сигналы, кроме сигналов:

- `rx_busy`, `rx_valid`, `rx_data`, `tx_busy` (т.к. те уже подключены к выходам модулей `uart_rx` и `uart_tx`),
- `send_fin`, `size_fin`, `flash_fin`, `next_round`, `flash_size_ascii`, `flash_addr_ascii`, `init_msg`, `flash_msg` (т.к. они уже реализованы в представленной выше логике).

Так же необходимо реализовать выходы модуля программатора:

- `instr_addr_o`;
- `instr_wdata_o`;
- `instr_we_o`;
- `data_addr_o`;
- `data_wdata_o`;
- `data_we_o`;
- `core_reset_o`.

##### Реализация конечного автомата

Для реализации сигналов `state`, `next_state` используйте граф переходов между состояниями, представленный на _рис. 3_. В случае, если не выполняется ни одно из условий перехода, автомат должен остаться в текущем состоянии.

Для работы логики переходов, необходимо реализовать счетчики `size_counter`, `flash_counter`, `msg_counter`.

`size_counter` должен сбрасываться в значение `4`, а также принимать это значение во всех состояниях кроме: `RCV_SIZE`, `RCV_NEXT_COMMAND`. В данных двух состояниях счётчик должен декрементироваться в случае, если `rx_valid` равен единице.

`flash_counter` должен сбрасываться в значение `flash_size`, а также принимать это значение во всех состояниях кроме `FLASH`. В этом состоянии счётчик должен декрементироваться в случае, если `rx_valid` равен единице.

`msg_counter` должен сбрасываться в значение `INIT_MSG_SIZE-1` (в _Листинге 5_ объявлены параметры `INIT_MSG_SIZE`, `FLASH_MSG_SIZE` и  `ACK_MSG_SIZE`).

`msg_counter` должен инициализироваться следующим образом:

- в состоянии `FLASH` должен принимать значение `FLASH_MSG_SIZE-1`,
- в состоянии `RCV_SIZE` должен принимать значение `ACK_MSG_SIZE-1`,
- в состоянии `RCV_NEXT_COMMAND`  должен принимать значение `INIT_MSG_SIZE-1`.

В состояниях: `INIT_MSG`, `SIZE_ACK`, `FLASH_ACK` `msg_counter` должен декрементироваться в случае, если `tx_valid` равен единице.

Во всех остальных ситуациях `msg_counter` должен сохранять свое значение.

##### Реализация сигналов, подключаемых к uart_tx

Сигнал `tx_valid` должен быть равен единице только когда `tx_busy` равен нулю, а конечный автомат находится в одном из следующих состояний:

- `INIT_MSG`,
- `SIZE_ACK`,
- `FLASH_ACK`

Иными словами, `tx_valid` равен единице, когда автомат находится в состоянии, отвечающем за передачу сообщений от программатора, но в данный момент программатор не отправляет очередной байт сообщения.

Сигнал `tx_data` должен нести очередной байт одного из передаваемых сообщений:

- в состоянии `INIT_MSG` передаётся очередной байт сообщения `init_msg`
- в состоянии `SIZE_ACK` передаётся очередной байт сообщения `flash_size`
- в состоянии `FLASH_ACK` передаётся очередной байт сообщения `flash_msg`.

В остальных состояниях он равен нулю. Для отсчёта байт используется счётчик `msg_counter`.

##### Реализация интерфейсов памяти инструкций и данных

Почему программатору необходимо два интерфейса? Дело в том, что в процессорной системе используется две шины: шина инструкций и шина данных. Чтобы не переусложнять логику системы дополнительным мультиплексированием, программатор также будет реализовывать два отдельных интерфейса. При этом необходимо различать, когда выполняется программирование памяти инструкций, а когда — памяти данных. Поскольку обе эти памяти имеют независимые адресные пространства, адреса по которым может вестись программирование могут быть неотличимы. Однако с этой же проблемой мы сталкивались и в ЛР№14 во время описания скрипта компоновщика. Тогда было решено дать секции данных специальный заведомо большой адрес загрузки. Это же решение отлично ложится и в логику программатора: если мы будет использовать при программировании системы заведомо большие адреса загрузки, по их значению мы сможем понимать назначение текущего блока данных: если адрес записи этого блока больше либо равен размеру памяти инструкций в байтах — этот блок не предназначен для памяти инструкций и будет отправлен на запись по интерфейсу памяти данных, в противном случае — наоборот.

Сигналы памяти инструкций (регистры `instr_addr_o`, `instr_wdata_o`, `instr_we_o`):

- по сигналу сброса — сбрасываются в ноль
- в случае состояния `FLASH` и пришедшего сигнала `rx_valid`, если значение `flash_addr` **меньше** размера памяти инструкций в байтах:
  - `instr_wdata_o` принимает значение `{instr_wdata_o[23:0], rx_data}` (справа вдвигается очередной пришедший байт)
  - `instr_we_o` становится равен `(flash_counter[1:0] == 2'b01)`
  - `instr_addr_o` становится равен `flash_addr + flash_counter - 1`
- во всех остальных ситуациях `instr_wdata_o` и `instr_addr_o` сохраняют свое значение, а `instr_we_o` сбрасывается в ноль.

Сигналы памяти данных (`data_addr_o`, `data_wdata_o`, `data_we_o`):

- по сигналу сброса — сбрасываются в ноль
- в случае состояния `FLASH` и пришедшего сигнала `rx_valid`, если значение `flash_addr` **больше либо равно** размеру памяти инструкций в байтах:
  - `data_wdata_o` принимает значение `{data_wdata_o[23:0], rx_data}` (справа вдвигается очередной пришедший байт)
  - `data_we_o` становится равен `(flash_counter[1:0] == 2'b01)`
  - `data_addr_o` становится равен `flash_addr + flash_counter - 1`
- во всех остальных ситуациях `data_wdata_o` и `data_addr_o` сохраняют свое значение, а `data_we_o` сбрасывается в ноль.

##### Реализация оставшейся части логики

Регистр `flash_size` работает следующим образом:

- по сигналу сброса — сбрасывается в 0;
- в состоянии `RCV_SIZE` при `rx_valid` равном единице становится равен `{flash_size[2:0], rx_data}` (сдвигается на 1 байт влево и на освободившееся место ставится очередной пришедший байт);
- в остальных ситуациях сохраняет свое значение.

Регистр `flash_addr` почти полностью повторяет поведение `flash_size`:

- по сигналу сброса — сбрасывается в 0;
- в состоянии `RCV_NEXT_COMMAND` при `rx_valid` равном единице становится равен `{flash_addr[2:0], rx_data}` (сдвигается на 1 байт влево и на освободившееся место ставится очередной пришедший байт);
- в остальных ситуациях сохраняет свое значение.

Сигнал `core_reset_o` равен единице в случае, если состояние конечного автомата не `FINISH`.

> Так как вышесказанное по сути является полным описанием работы программатора на русском языке, то фактически **задача сводится к переводу** текста описания программатора **с русского на SystemVerilog**.

### Интеграция программатора в processor_system

![../../.pic/Labs/lab_15_programming_device/fig_04.drawio.svg](../../.pic/Labs/lab_15_programming_device/fig_04.drawio.svg)

_Рисунок 4. Интеграция программатора в `processor_system`._

В первую очередь, необходимо заменить память инструкций и добавить новый модуль. После чего подключить программатор к памяти инструкций и мультиплексировать выход интерфейса памяти данных программатора с интерфейсом памяти данных LSU. Сигнал сброса процессора необходимо заменить на выход `core_reset_o`.

В случае, если использовалось периферийное устройство `uart_tx`, необходимо мультиплексировать его выход `tx_o` с одноименным выходом программатора аналогично тому, как это было сделано с сигналами интерфейса памяти данных.

### Пример загрузки программы

Чтобы проверить работу программатора на практике необходимо подготовить скомпилированную программу подобно тому, как это делалось в ЛР№14 (или взять готовые .mem-файлы вашего варианта из ЛР№13). Однако, в отличие от ЛР№14, удалять первую строчку из файла, инициализирующего память данных не надо — теперь адрес загрузки будет использоваться в процессе загрузки.

Необходимо подключить отладочный стенд к последовательному порту компьютера (в случае платы Nexys A7 — достаточно просто подключить плату usb-кабелем, как это делалось на протяжении всех лабораторных для прошивки). Необходимо будет узнать COM-порт, по которому отладочный стенд подключен к компьютеру. Определить нужный COM-порт на операционной системе Windows можно через "Диспетчер устройств", который можно открыть через меню пуск. В данном окне необходимо найти вкладку "Порты (COM и LPT)", раскрыть её, а затем подключить отладочный стенд через USB-порт (если тот еще не был подключен). В списке появится новое устройство, а в скобках будет указан нужный COM-порт.

Подключив отладочный стенд к последовательному порту компьютера и сконфигурировав ПЛИС вашим проектом, остается проинициализировать память. Сделать это можно с помощью предоставленного скрипта, пример запуска которого приведен в листинге 6.

```bash
# Пример использования скрипта. Сперва указываются опциональные аргументы
# (инициализация памяти данных и различных областей памяти vga-контроллера),
# Затем идут обязательные аргументы: файл для прошивки памяти инструкций и
# COM-порт.
$ python flash.py --help
usage: flash.py [-h] [-d DATA] [-c COLOR] [-s SYMBOLS] [-t TIFF] instr comport

positional arguments:
  instr                 File for instr mem initialization
  comport               COM-port name

optional arguments:
  -h, --help            show this help message and exit
  -d DATA, --data DATA  File for data mem initialization
  -c COLOR, --color COLOR
                        File for color mem initialization
  -s SYMBOLS, --symbols SYMBOLS
                        File for symbols mem initialization
  -t TIFF, --tiff TIFF  File for tiff mem initialization

python3 flash.py -d /path/to/data.mem -c /path/to/col_map.mem \
        -s /path/to/char_map.mem -t /path/to/tiff_map.mem /path/to/program COM
```

_Листинг 6. Пример использования скрипта для инициализации памяти._

## Порядок выполнения задания

1. Опишите модуль `rw_instr_mem`, используя код, представленный в _листинге 4_.
2. Добавьте пакет [`bluster_pkg`](bluster_pkg.sv), содержащий объявления параметров и вспомогательных вызовов, используемых модулем и тестбенчем.
3. Опишите модуль `bluster`, используя код, представленный в _листинге 5_. Завершите описание этого модуля.
   1. Опишите конечный автомат используя сигналы `state`, `next_state`, `send_fin`, `size_fin`, `flash_fin`, `next_round`.
   2. [Реализуйте](#реализация-конечного-автомата) логику счетчиков `size_counter`, `flash_counter`, `msg_counter`.
   3. [Реализуйте](#реализация-сигналов-подключаемых-к-uart_tx) логику сигналов `tx_valid`, `tx_data`.
   4. [Реализуйте](#реализация-интерфейсов-памяти-инструкций-и-данных) интерфейсы памяти инструкций и данных.
   5. [Реализуйте](#реализация-оставшейся-части-логики) логику оставшихся сигналов.
4. Проверьте модуль с помощью верификационного окружения, представленного в файле [`lab_15.tb_bluster.sv`](lab_15.tb_bluster.sv). В случае, если в TCL-консоли появились сообщения об ошибках, вам необходимо [найти](../../Vivado%20Basics/05.%20Bug%20hunting.md) и исправить их.
   1. Перед запуском моделирования убедитесь, что у вас выбран корректный модуль верхнего уровня в `Simulation Sources`.
   2. Для работы тестбенча потребуется пакет [`peripheral_pkg`](../13.%20Peripheral%20units/peripheral_pkg.sv) из ЛР№13, а также файлы [`lab_15_char.mem`](lab_15_char.mem), [`lab_15_data.mem`](lab_15_data.mem), [`lab_15_instr.mem`](lab_15_instr.mem) из папки [mem_files](mem_files).
5. Интегрируйте программатор в модуль `processor_system`.
   1. В модуле `processor_system` замените память инструкцией модулем `rw_instr_mem`.
   2. Добавьте в модуль `processor_system` экземпляр модуля-программатора.
      1. Интерфейс памяти инструкций подключается к порту записи модуля `rw_instr_mem`.
      2. Интерфейс памяти данных мультиплексируется с интерфейсом памяти данных модуля `LSU`.
      3. Замените сигнал сброса модуля `processor_core` сигналом `core_reset_o`.
      4. В случае если у вас есть периферийное устройство `uart_tx` его выход `tx_o` необходимо мультиплексировать с выходом `tx_o` программатора аналогично тому, как был мультиплексирован интерфейс памяти данных.
6. Проверьте процессорную систему после интеграции программатора с помощью верификационного окружения, представленного в файле [`lab_15.tb_processor_system.sv`](lab_15.tb_processor_system.sv).
   1. Данный тестбенч необходимо обновить под свой вариант. Найдите строки со вспомогательным вызовом `program_region`, первыми аргументами которого являются "YOUR_INSTR_MEM_FILE" и "YOUR_DATA_MEM_FILE". Обновите эти строки под имена файлов, которыми вы инициализировали свои память инструкций и данных в ЛР№13. Если память данных вы не инициализировали, можете удалить/закомментировать соответствующий вызов. При необходимости вы можете добавить столько вызовов, сколько вам потребуется.
   2. В .mem-файлах, которыми вы будете инициализировать вашу память необходимо сделать доработку. Вам необходимо указать адрес ячейки памяти, с которой необходимо начать инициализировать память. Это делается путём добавления в начало файла строки вида: `@hex_address`. Пример `@FA000000`. Строка обязательно должна начинаться с символа `@`, а адрес обязательно должен быть в шестнадцатеричном виде. Для памяти инструкций нужен нулевой адрес, а значит нужно использовать строку `@00000000`. Для памяти данных необходимо использовать адрес, превышающий размер памяти инструкций, но не попадающий в адресное пространство других периферийных устройств (старший байт адреса должен быть равен нулю). Поскольку система использует байтовую адресацию, адрес ячеек будет в 4 раза меньше адреса по которому обратился бы процессор. Это значит, что если бы вы хотели проинициализировать память VGA-контроллера, вам нужно было бы использовать не адрес `@07000000`, а `@01C00000` (`01C00000 * 4 = 07000000`). Таким образом, для памяти данных оптимальным адресом инициализации будет `@00200000`, поскольку эта ячейка с адресом `00200000` соответствует адресу `00800000` — этот адрес не накладывается на адресное пространство других периферийных устройств, но при этом заведомо больше возможного размера памяти инструкций. Примеры использования начальных адресов вы можете посмотреть в файлах [`lab_15_char.mem`](lab_15_char.mem), [`lab_15_data.mem`](lab_15_data.mem), [`lab_15_instr.mem`](lab_15_instr.mem) из папки [mem_files](mem_files).
   3. Тестбенч будет ожидать завершения инициализации памяти, после чего сформирует те же тестовые воздействия, что и в тестбенче к ЛР№13. А значит, если вы использовали для инициализации те же самые файлы, поведение вашей системы после инициализации не должно отличаться от поведения на симуляции в ЛР№13.
   4. Перед запуском моделирования убедитесь, что у вас выбран корректный модуль верхнего уровня в `Simulation Sources`.
7. Переходить к следующему пункту можно только после того, как вы полностью убедились в работоспособности системы на этапе моделирования (увидели, что в память инструкций и данных были записаны корректные данные, после чего процессор стал обрабатывать прерывания от устройства ввода). Генерация битстрима будет занимать у вас долгое время, а итогом вы получите результат: заработало/не заработало, без какой-либо дополнительной информации, поэтому без прочного фундамента на моделировании далеко уехать у вас не выйдет.
8. Подключите к проекту файл ограничений ([nexys_a7_100t.xdc](../13.%20Peripheral%20units/nexys_a7_100t.xdc)), если тот ещё не был подключён, либо замените его содержимое данными из файла, представленного в ЛР№13.
9. Проверьте работу вашей процессорной системы на отладочном стенде с ПЛИС.
   1. Для инициализации памяти процессорной системы используется скрипт [flash.py](flash.py).
   2. Перед инициализацией необходимо подключить отладочный стенд к последовательному порту компьютера и узнать номер этого порта (см. [пример загрузки программы](#пример-загрузки-программы)).
   3. Формат файлов для инициализации памяти с помощью скрипта аналогичен формату, использовавшемуся в [тестбенче](lab_15_tb_bluster.sv). Это значит что первой строчкой всех файлов должна быть строка, содержащая адрес ячейки памяти, с которой должна начаться инициализация (см. п. 6.2).
10. В текущем исполнении инициализировать память системы можно только 1 раз с момента сброса, что может оказаться не очень удобным при отладке программ. Подумайте, как можно модифицировать конечный автомат программатора таким образом, чтобы получить возможность в неограниченном количестве инициализаций памяти без повторного сброса всей системы.

## Список источников

1. [Finite-state machine](https://en.wikipedia.org/wiki/Finite-state_machine).
2. [All about circuits — Finite State Machines](https://www.allaboutcircuits.com/textbook/digital/chpt-11/finite-state-machines/)
