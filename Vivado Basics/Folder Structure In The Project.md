# Структура папок в проекте Vivado

Вы смотрите на окно `Sources` и ничего не понимаете? Или создали модуль, а он куда–то исчез? Или просто хотите понять, как лучше ориентироваться в созданных модулях? Тогда это для вас.

В левом верхнем углу Vivado расположено окно со вкладкой `Sources`. Здесь располагается иерархия модулей вашего проекта. Если у вас нет этой вкладки, открыть её можно так: `Window –> Sources`.

![../.pic/Vivado%20Basics/Folder%20Structure%20In%20The%20Project/folder_structure_1.png](../.pic/Vivado%20Basics/Folder%20Structure%20In%20The%20Project/folder_structure_1.png)

Во вкладке `Design Sources` хранятся модули, описывающие ваш дизайн. В `Constrain` лежат файлы, необходимые для работы с конкретной ПЛИС. `Simulation Sources` хранит в себе тестбенчи и обычные модули.

Допустим, мы создали модуль полного однобитного сумматора `fulladder`, а также создали и планируем описать модуль полного четырехбитного сумматора `fulladder4`, подключив к нему четыре однобитных.

Итак, раскрываем вкладку `Design Sources` и видим два модуля – `fulladder` и `fulladder4`, которые пока что никак друг с другом не связаны. Двойное нажатие на название модуля приведёт к его открытию.

![../.pic/Vivado%20Basics/Folder%20Structure%20In%20The%20Project/folder_structure_2.png](../.pic/Vivado%20Basics/Folder%20Structure%20In%20The%20Project/folder_structure_2.png)

Модуль `fulladder4` является модулем верхнего уровня (top-level module), то есть, если мы запустим синтез или имплементацию проекта, именно этот модуль Vivado будет рассматривать. Чтобы сменить модуль верхнего уровня, необходимо нажать на выбранный модуль правой кнопкой мыши, затем на `Set a top`.

![../.pic/Vivado%20Basics/Folder%20Structure%20In%20The%20Project/folder_structure_3.png](../.pic/Vivado%20Basics/Folder%20Structure%20In%20The%20Project/folder_structure_3.png)

Подключим `fulladder` к `fulladder4` для создания четырехбитного сумматора путём соединения четырех однобитных. Тогда после сохранения окно изменится так:

![../.pic/Vivado%20Basics/Folder%20Structure%20In%20The%20Project/folder_structure_4.png](../.pic/Vivado%20Basics/Folder%20Structure%20In%20The%20Project/folder_structure_4.png)

Раскроем вкладку `fulladder4` и увидим 4 подключенных модуля `fulladder`:

![../.pic/Vivado%20Basics/Folder%20Structure%20In%20The%20Project/folder_structure_5.png](../.pic/Vivado%20Basics/Folder%20Structure%20In%20The%20Project/folder_structure_5.png)

В `Simulation Sources` мы видим один файл тестбенча, к которому что-то подключено, и модуль `fulladder4` с подключенными к нему другими модулями:

![../.pic/Vivado%20Basics/Folder%20Structure%20In%20The%20Project/folder_structure_6.png](../.pic/Vivado%20Basics/Folder%20Structure%20In%20The%20Project/folder_structure_6.png)

Модули из `Design Sources` автоматически попадают в `Simulation Sources`, так как эти файлы нужны для симуляции. Они не являются копиями модулей, а просто дублируются для удобства. Каждый раз, когда вы меняете что-то в своём дизайне, это отражается как во вкладке `Design Sources`, так и в `Simulation Sources`. Раскроем вкладку с модулем `tb`:

![../.pic/Vivado%20Basics/Folder%20Structure%20In%20The%20Project/folder_structure_7.png](../.pic/Vivado%20Basics/Folder%20Structure%20In%20The%20Project/folder_structure_7.png)

Такая картина говорит нам о попытке подключить модуль, которого нет в проекте. Часто это связано с неправильным указанием подключаемого модуля. В данном случае мы хотим подключить модуль `half_adder` и Vivado не может его найти.

```Verilog
module tb();
...
half_adder DUT(
  .A    (a),
  .B    (b),
  .P    (p),
  .S    (s)
);
...
```

Переименуем название подключаемого модуля на `fulladder4` и сохраним.

```Verilog
module tb();
...
fulladder4 DUT(
  .A    (a),
  .B    (b),
  .P    (p),
  .S    (s)
);
...
```

После обновления в окне `Sources` модуль `fulladder4` "спрячется" под `tb`. Если раскрыть вкладку, будет видно, что `fulladder4` подключен к `tb`, а четыре модуля `fulladder` – к `fulladder4`. Также отметим, что `tb` является модулем верхнего уровня, значит, если мы захотим запустить симуляцию, то Vivado выполнит симуляцию именно для модуля `tb`. Изменить модуль верхнего уровня можно так же, как было описано ранее.

![../.pic/Vivado%20Basics/Folder%20Structure%20In%20The%20Project/folder_structure_8.png](../.pic/Vivado%20Basics/Folder%20Structure%20In%20The%20Project/folder_structure_8.png)
