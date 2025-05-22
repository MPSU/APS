# Список исправлений

![http://95.215.8.74:5000/days_since_last_commit.png](http://95.215.8.74:5000/days_since_last_commit.png)

**22.05.2025**: Исправлено несоответствие в названиях модулей в ЛР10-12.

- `irq_controller` следует читать как `interrupt_controller`;
- `processor_unit` следует читать как `processor_system`.

В рисунке II.12-3 добавлена разрядность сигнала `irq_ret_o` (должна быть 16 бит).

<details>
<summary> Обновлённый рисунок </summary>

![.pic/Labs/lab_12_daisy_chain/fig_03.drawio.svg](.pic/Labs/lab_12_daisy_chain/fig_03.drawio.svg)

_Рисунок II.8-3. Структурная схема блока приоритетных прерываний._

</details>

---

**13.05.2025**: Исправлен рисунок II.8-3 — исправлена опечатка в названии нижнего сигнала (`mem_wd_i` → `mem_wd_o`).

<details>
<summary> Обновлённый рисунок </summary>

![.pic/Labs/lab_08_lsu/fig_03.wavedrom.svg](.pic/Labs/lab_08_lsu/fig_03.wavedrom.svg)

Рисунок II.8-3. Временна́я диаграмма запросов на запись со стороны ядра и сигнала mem_wd_o.

</details>

---

**29.03.2025**: Исправлен рисунок II.4-4 — убрана логика безусловного перехода, т.к. она должна была появиться только в следующем параграфе.

<details>
<summary> Обновлённый рисунок </summary>

![.pic/Labs/lab_04_cybercobra/ppd_4.drawio.svg](.pic/Labs/lab_04_cybercobra/ppd_4.drawio.svg)

Рисунок II.4-4. Реализация условного перехода.

</details>
