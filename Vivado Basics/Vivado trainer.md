# Создание базового проекта с прошивкой ПЛИС в Vivado

## Создание проекта в Системе Автоматизированного Проектирования (САПР)

1. Запустить Vivado
2. Нажать `Create Project`
3. В открывшемся окне нажать Next
4. Ввести название проекта (никаких пробелов и кириллических символов) → Выбрать папку для проектов (создать каталок на D:/) → Поставить галку `Create project subdirectory` → Нажать `Next`
5. Выбрать RTL Project → Поставить галку `Do not specify sources at this time` → Нажать Next
6. Выставить фильтры, для сужения списка ПЛИС:
   * Family: `Artix 7`
   * Package: `CSG324`,
   * Speed: `-1`.

<details>
   <summary> Скриншот окна с выставленными фильтрами</summary>

   ![../.pic/Vivado%20Basics/Vivado%20trainer/fig_01.png](../.pic/Vivado%20Basics/Vivado%20trainer/fig_01.png)

</details>

1. В списке выбрать ПЛИС `xc7a100tcsg324-1` → Нажать Next
2. Нажать Finish
3. Закрыть Vivado
4. Удалить папку
5. Повторить все действия самостоятельно

## Создание модуля на SystemVerilog

1. Создать новый SystemVerilog файл, для этого в окне `Sources` нажать на кнопку `+`
2. В открывшемся окне выбрать `Add or create design source` → Нажать `Next`
3. Нажать `Create File` → В открывшемся окне ввести имя модуля `top` и выбрать тип файла SystemVerilog → Нажать `OK` → В оставшемся окне нажать `Finish`
4. В открывшемся окне НЕ вводить названия портов и сразу нажать OK → После чего подтвердить выбор `Yes`
5. Двойным кликов в окне `Source` открыть файл `top.sv`
6. Написать следующий код:

```SystemVerilog
module top (
  input  logic clk,
  input  logic a,
  input  logic b,
  output logic q
);

logic c;

assign c = a ^ b;

always_ff @(posedge clk) begin
 q <= c;
end

endmodule
```

7. Сохранить изменения
8. Нажать `Open Elaborated Design`
9.  Нажать `Schematic` в открывшемся списке
10. Проанализировать полученный результат (сопоставить с SystemVerilog-описанием)
11. Закрыть проект

## Реализация простого проекта на отладочном стенде

1. Создать новый проект
2. Создать новый SystemVerilog файл с названием `basic`
3. Написать следующий код:

```SystemVerilog
module basic (
  input  logic [15:0] SW,
  output logic [15:0] LED
);

assign LED[0] = SW[0] & SW[1];
assign LED[2] = SW[2] | SW[3];
assign LED[4] = SW[4] ^ SW[5];
assign LED[10:6] = ~SW[10:6];
assign LED[13:11] = {SW[11], SW[12], SW[13]};
assign LED[15:14] = { 2{SW[14]} };

endmodule

```

4. Сохранить изменения
5. В окне Sources нажать на кнопку `+`
6. В открывшемся окне выбрать `Add or create constraints` → Нажать Next
7. Нажать `Create File` → В открывшемся окне ввести название → Нажать `OK` → `Finish`
8. В окне `Source` в открывающемся списке `Constraints` найти только что созданный файл и открыть его для редактирования двойным щелчком
9.  Скопировать содержимое файла констрейнов с [официального сайта](https://github.com/Digilent/digilent-xdc) и вставить в только что созданный → Найти строки посвященные SW и LED и раскомментировать их → Сохранить изменения
10. `Run Synthesis`
11. `Run Implementation`
12. После успешной имплементации нажимаем `Generate Bitstream` для генерации файла прошивки
13. Аккуратно достаем и подключаем стенд к компьютеру → Включаем питание на плате
14. Нажимаем `Open Hardware Manager` (под `Generate Bitstream`)
15. Вместо окна `Source` будет отображаться окно `Hardware`, в нем необходимо нажать кнопку `Auto Connect`  (единственная активная кнопка) → В окне появится подключенное устройство
16. Нажать правой кнопкой на устройстве `xc7a100t_0` → Выбрать пункт меню `Program Device`
17. В открывшемся окне нажать `Program`
18. Сопоставить поведение отладочной платы с SystemVerilog-описанием
