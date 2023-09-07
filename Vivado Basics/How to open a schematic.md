# Как открыть цифровую схему проекта

**Вы написали модуль, но не знаете, как открыть цифровую схему?**

Сохраняем модуль –> Слева на панели управления раскрываем вкладку RTL ANALYSIS –> Раскрываем вкладку Open Elaborated Design –> Нажимаем на Schematic:

![../.pic/Vivado%20Basics/How%20to%20open%20a%20schematic/open_schematic_1.png](../.pic/Vivado%20Basics/How%20to%20open%20a%20schematic/open_schematic_1.png)

`Обратите внимание, что во вкладках SYNTHESIS и IMPLEMENTATION также есть возможность открыть Schematic. Запуск в них строит схему на основе примитивных компонентов ПЛИС. В данной лабораторной работе нам интересна именно цифровая схема, собранная из логических элементов. Получить её можно только во вкладке RTL ANALYSIS.`

Нажимаем ОК:

![../.pic/Vivado%20Basics/How%20to%20open%20a%20schematic/open_schematic_2.png](../.pic/Vivado%20Basics/How%20to%20open%20a%20schematic/open_schematic_2.png)

Ждём или нажимаем background, чтобы синтез схемы выполнялся в фоновом режиме:

![../.pic/Vivado%20Basics/How%20to%20open%20a%20schematic/open_schematic_3.png](../.pic/Vivado%20Basics/How%20to%20open%20a%20schematic/open_schematic_3.png)

После этого во вкладке Schematic вы должны увидеть свою схему:

![../.pic/Vivado%20Basics/How%20to%20open%20a%20schematic/open_schematic_6.png](../.pic/Vivado%20Basics/How%20to%20open%20a%20schematic/open_schematic_6.png)

<br>

**Вы обновили модуль, но схема осталась прежней?**

Сохраняем модуль –> Сверху над схемой появилась желтая полоса, нажимаем Reload:

![../.pic/Vivado%20Basics/How%20to%20open%20a%20schematic/open_schematic_4.png](../.pic/Vivado%20Basics/How%20to%20open%20a%20schematic/open_schematic_4.png)

Ждём загрузку... и вот она, наша новая схема:

![../.pic/Vivado%20Basics/How%20to%20open%20a%20schematic/open_schematic_5.png](../.pic/Vivado%20Basics/How%20to%20open%20a%20schematic/open_schematic_5.png)
