# Как открыть цифровую схему проекта

Одним из способов первичной оценки результатов описания модуля является просмотр логической схемы, построенной по описанию этого модуля. Порядок открытия схемы следующий:

Сохраняем модуль → Слева на панели управления раскрываем вкладку `RTL ANALYSIS` → Раскрываем вкладку `Open Elaborated Design` → Нажимаем на `Schematic`.

![../.pic/Vivado%20Basics/How%20to%20open%20a%20schematic/fig_1.png](../.pic/Vivado%20Basics/How%20to%20open%20a%20schematic/fig_1.png)

_Рисунок 1. Расположение кнопки `Schematic`._

Нажатие на `Schematic` приведет к появлению окна `Elaborate Design`, в котором необходимо будет нажать на кнопку `OK`.

![../.pic/Vivado%20Basics/How%20to%20open%20a%20schematic/fig_2.png](../.pic/Vivado%20Basics/How%20to%20open%20a%20schematic/fig_2.png)

_Рисунок 2. Окно `Elaborate Design`.

После нажатия на `OK`, появится окно `Open Elaborated Design`, которое автоматически пропадет по завершению процесса. В случае если вы компилируете крупный проект и хотите продолжить работу во время компиляции, вы можете нажать на кнопку `Background`.

![../.pic/Vivado%20Basics/How%20to%20open%20a%20schematic/fig_3.png](../.pic/Vivado%20Basics/How%20to%20open%20a%20schematic/fig_3.png)

_Рисунок 3. Окно `Open Elaborated Design`._

После этого в окне `Project Manager` появится вкладка `Schematic`, где вы должны увидеть свою схему:

![../.pic/Vivado%20Basics/How%20to%20open%20a%20schematic/fig_4.png](../.pic/Vivado%20Basics/How%20to%20open%20a%20schematic/fig_4.png)

_Рисунок 4. Открывшаяся схема модуля._

> Обратите внимание, что во вкладках SYNTHESIS и IMPLEMENTATION также есть возможность открыть Schematic. Запуск в них строит схему на основе примитивов ПЛИС (см. "Этапы реализации проекта в ПЛИС"). В рамках лабораторных работ нам будет интересна именно цифровая схема, собранная из логических элементов, которая открывается при нажатии на `Schematic` во вкладке RTL ANALYSIS.`

## Как обновить схему после правок модуля

После правок в модуле, необходимо отобразить обновленную схему. Повторное нажатие на `Schematic` приведет лишь к открытию ещё одной вкладки со старой версией схемы.

Однако, после изменения модуля вы можете обратить внимание на появление светло-жёлтого уведомления вверху окна `Project Manager`, где будет сказано о том, что построенный проект устарел, т.к. исходники были изменены, а рядом с ним — кнопку "Reload" (см. _рис. 5_). Нажатие по этой кнопке приведет к рекомпиляции проекта и открытию обновленной схемы.

![../.pic/Vivado%20Basics/How%20to%20open%20a%20schematic/fig_5.png](../.pic/Vivado%20Basics/How%20to%20open%20a%20schematic/fig_5.png)

_Рисунок 5. Кнопка повторной загрузки схемы._

## Дополнительные материалы

Подробнее о взаимодействии с окном схемы можно прочитать в руководстве пользователя Vivado: ["Vivado Design Suite User Guide: Using the Vivado IDE (UG893)"](https://docs.xilinx.com/r/en-US/ug893-vivado-ide) (раздел ["Using the Schematic Window"](https://docs.xilinx.com/r/en-US/ug893-vivado-ide/Using-the-Schematic-Window)).
