# Как добавить файл с define

 Директива `ˋinclude` позволяет вставлять код из одного файла, в код другого, подобно `#include` на языке `C`. Если вы описываете данную директиву, когда подключаемый файл не добавлен в качестве Verilog Header в проект, Vivado будет интерпретировать её как синтаксическую ошибку, поскольку не сможет найти подключаемый файл, и тогда ваш модуль будет находиться в папке `Syntax Error Files` иерархии вашего проекта.

![../.pic/Vivado%20Basics/Verilog%20Header/Verilog_Header1.png](../.pic/Vivado%20Basics/Verilog%20Header/Verilog_Header1.png)

Файл в проект добавляется точно так же, как при создании Verilog-файла, только вместо `Create File` нужно нажать `Add Files`, затем перейти к его расположению, выбрать его и нажать `OK` и `Finish`.

После обновления иерархии вашего проекта, этот файл будет располагаться в папке `Non-module Files`.

![../.pic/Vivado%20Basics/Verilog%20Header/Verilog_Header2.png](../.pic/Vivado%20Basics/Verilog%20Header/Verilog_Header2.png)

Следующим шагом нужно нажать по этому файлу `ПКМ`, выделив его, убедившись, что в окне ниже выбран именно он, необходимо сменить его тип на `Verilog Header`.

![../.pic/Vivado%20Basics/Verilog%20Header/Verilog_Header3.png](../.pic/Vivado%20Basics/Verilog%20Header/Verilog_Header3.png)

После этого нужно убедиться, что наш файл появился в иерархии проекта в папке `Verilog Header`, а наш файл с модулем больше не лежит в папке `Syntax Error Files`.

![../.pic/Vivado%20Basics/Verilog%20Header/Verilog_Header4.png](../.pic/Vivado%20Basics/Verilog%20Header/Verilog_Header4.png)
