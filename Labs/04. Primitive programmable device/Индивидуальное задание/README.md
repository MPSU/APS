# Writing a Program for the CYBERcobra Processor

To fully grasp the principles behind the processor you have built, you need to write one of the [individual assignments](#individual-assignments). The variant is assigned by the instructor.

The procedure is as follows:

1. First, read the assignment carefully and study the example provided at the end. If you have any questions about the assignment or the example, contact the instructor. The better you understand what is expected of you, the easier it will be to complete the task.
2. Design the program algorithm (literally take a sheet of paper and draw a flowchart). Before you dive into the exciting adventure of zeros and ones, you need to draw a clear map of your journey.
3. Verify your flowchart against the data from the example. If everything matches, check your flowchart against other data. Do not forget about edge cases (negative numbers, division by zero, overflows, etc. — these may differ for each assignment).
4. Once you have confirmed that the algorithm works for all possible inputs, it is time to implement it as a binary program.
5. The program is described in a text file. For convenience, a special converter has been written that takes a text file containing comments and binary code separated by spaces as input, and produces a text file that can be used to initialize the instruction memory. For more details on the converter, see the [cyberconverter](#cyberconverter) section. An example of a text file that the converter can accept:

    ```text
    //J B WS ALUop  RA1   RA2   const     WA
      0 0 00   11111111111111111111111  00001  // load constant -1 into register 1
      0 0 10   00000000000000000000000  00010  // load value from sw_i input into register 2
      0 0 00   00000000000000000000001  00011  // load constant 1 into register 3
      0 0 01 00000 00001 00011 00000000 00001  // add register 1 and register 3, store result in register 1
      0 1 00 11110 00001 00010 11111111 00000  // if the value in register 1 is less than the value in register 2, go back 1 instruction
      1 0 00 00000 00001 00000 00000000 00000  // repeat this instruction indefinitely, outputting the value of register 1 to out_o
    ```

6. When implementing conditional branches, keep the following rules in mind:
   1. A branch block (analogous to `if/else`) consists of two sets of instructions:
      1. instructions of the `if` block (executed when the condition is true)
      2. instructions of the `else` block (executed when the condition is false)

      The instructions of the `else` block immediately follow the branch instruction (because when the branch condition is not taken, `PC` moves to the next instruction).  
      To prevent the `if` block instructions from being executed after the `else` block completes, an unconditional jump to the instruction following the `if` block must be added at the end of the `else` block.
   2. If you are implementing not a branch (analogous to `if/else`) but only a condition check for a block of instructions (analogous to an `if` block without an `else`), remember that the `else` block still exists — it simply contains no instructions. However, as in the previous rule, you must still add an unconditional jump to the instruction following the `if` block.  
      This can be avoided by inverting your condition. In that case, if the inverted condition is true, you can immediately skip the required number of instructions and begin executing the instruction beyond your `if` block. If the inverted condition is false (i.e., the original condition is true), `PC` will move to the next instruction, where your `if` block instructions will be located.  
      This sounds somewhat confusing, so let us look at a couple of examples. We will first write the idea in C, then translate it into binary code for the CYBERcobra architecture:

      ```C
      if(reg[1]==reg[5])
      {
        reg[2] = 10;
        reg[3] = 15;
      }
      else
      {
        reg[2] = 7;
        goto if_end;  // Since in program memory the else block follows
                      // immediately after the conditional branch instruction,
                      // an unconditional jump must be added at the end
                      // to avoid executing the if block instructions.
      }
      if_end:
      ```

      We want to check whether the values in the register file at addresses `1` and `5` are equal. If so, write values `10` and `15` to addresses `2` and `3` respectively. Otherwise, write value `7` to address `2`.  
      This can be implemented with the following binary program:

      ```text
      //J B WS ALUop  RA1   RA2   const     WA
        0 1 00 11000 00001 00101 00000011 00000 // If registers 1 and 5 are equal,
                                                // move PC 3 instructions forward
                                                // (skip over two
                                                // instructions of the else block)
      //---------------------------------------
      // else block
      //---------------------------------------
        0 0 00   00000000000000000000111  00010 // reg[2] = 7
        1 0 00 00000 00000 00000 00000011 00000 // goto if_end
      //---------------------------------------


      //---------------------------------------
      // if block
      //---------------------------------------
        0 0 00   00000000000000000001010  00010 // reg[2] = 10
        0 0 00   00000000000000000001111  00011 // reg[3] = 15
      //---------------------------------------

        0 0 00   00000000000000000000000  00000 // some instruction at the if_end label,
                                                // where PC will be moved after
                                                // the else block executes
      ```

      Let us consider the second example, where there is no `else` block:

      ```C
      if(reg[1] == reg[5])
      {
        reg[2] = 10;
        reg[3] = 15;
      }
      ```

      As mentioned earlier, this conditional branch can be implemented using the same scheme (in which case the C program looks like):

      ```C
      if(reg[1] == reg[5])
      {
        reg[2] = 10;
        reg[3] = 15;
      }
      else
      {
        goto if_end;
      }
      if_end:
      ```

      Alternatively, the condition can be inverted:

      ```C
      if(reg[1] != reg[5])
      {

      }
      else
      {
        reg[2] = 10;
        reg[3] = 15;
      }
      ```

      In this case, there is no need to add an unconditional jump to the instruction following the `if` block, since there are no instructions there.  
      This condition can be implemented with the following binary program:

      ```text
      //J B WS ALUop  RA1   RA2   const     WA
        0 1 00 11001 00010 00101 00000011 00000 // If registers 2 and 5 are NOT EQUAL,
                                                // move PC 3 instructions forward
                                                // (skip over two
                                                // instructions of the else block)
      //---------------------------------------
      // else block
      //---------------------------------------
        0 0 00   00000000000000000001010  00010 // reg[2] = 7
        0 0 00   00000000000000000001111  00011 // reg[3] = 15
      //---------------------------------------
      ```

7. In binary programming, loops are best implemented as the equivalent of `do while` in C (if you are certain that the first iteration will always satisfy the loop exit condition). In this case, you first describe the loop body, then use a conditional branch to return to the beginning of the loop body. If the condition is not satisfied, execution will automatically exit the loop.
8. To make it easy to see the result at the end of program execution, add an unconditional jump instruction at the end of the program with the `const` field equal to zero. This will execute `PC=PC+0`, causing that instruction to repeat indefinitely. Set the `RA1` field to the address of the register holding the result. On the waveform, this will appear as all processor signals "freezing" at some point, while the output `out_o` holds the result computed by your program.
9. After writing the program, it must be verified. To do this, first convert it to the format accepted by the instruction memory using the [`cyberconverter`](#cyberconverter) tool. If necessary, replace the data in the instruction memory initialization file with the updated data.
10. If your program uses data from external devices, set the value you want to test on the `sw_i` input of the `CYBERcobra` module in the `testbench`.
11. Program verification is performed in the same way as verifying the `CYBERcobra` module — you expose the internal signals of the module and observe the behavior of: `PC`, `read_data` of the instruction memory, `flag` of the ALU, and the contents of the register file. Verify that at the end of execution, the output `out_o` holds the correct value.

## cyberconverter

[cyberconverter](cyberconverter.cpp) is a program that converts a text file containing CYBERcobra architecture instructions into a text file that can be used to initialize the instruction memory.

cyberconverter can process files containing comments (starting with `//`), spaces and blank lines, as well as sequences of `0` and `1` characters. Comments, spaces, and blank lines are removed, after which the remaining 32-character binary strings are converted to hexadecimal values and written to the output file.

cyberconverter accepts up to two arguments. The usage is as follows:

1. Display help:

    ```bash
    cyberconverter -h
    cyberconverter --help
    ```

2. Convert a program stored in `test.txt` and write the result to `program.mem`:

    ```bash
    cyberconverter test.txt program.mem
    ```

3. If the second argument is not specified, the result will be written to:
 `<source_filename>_converted.<source_file_extension>`:

    ```bash
    cyberconverter test.txt
    ```

     The result will be written to `test_converted.txt`.

4. If the program is run without any arguments, the source file is assumed to be `program.mem`.

If the source file is missing, contains unsupported characters, or has an incorrect instruction length, an error message will be displayed.

## Individual Assignments

In the assignments below, `a` refers to a number defined in the program (for example, the program sets `a=10`), and `sw_i` refers to the external device input. "Output to `out_o`" means that at the end of the program you must implement an infinite loop with `RA1` set to the address of the register holding the result (see step 8 of the "[Writing a Program for the CYBERcobra Processor](#writing-a-program-for-the-cybercobra-processor)" section).

If the assignment is used for writing an assembly program, `sw_i` denotes another number defined in the program (like `a`), and "Output to `out_o`" means writing the result to register `x10` (whose designated purpose is to return a function result) at the end of program execution.

1. Compute the [circular shift](https://ru.wikipedia.org/wiki/Битовый_сдвиг#Циклический_сдвиг) right `a >> sw_i`.  
Example: `a = 0...01011`, `sw_i = 0...010`.  
Result: `out_o = 110...010`.  

2. Compute `a - sw_i` without using the subtraction operation.  
Example: `sw_i = 0...011`, `a = 0...0100`.  
Result: `out_o = 0...001`.

3. Compute the [circular shift](https://ru.wikipedia.org/wiki/Битовый_сдвиг#Циклический_сдвиг) left `a << sw_i`.  
Example: `a = 10...01011`, `sw_i = 0...10`.  
Result: `out_o = 0...0101110`.  

4. Swap bits `[7:0]` and `[15:8]` of the number `sw_i`. Output the result to `out_o`.  
Example: `sw_i = 0...010100000_1110010`.  
Result: `out_o = 0...011100101_10100000`.   

5. Compute the approximate length of the vector `(a; sw_i)`. It is computed as `max + min/2`, where `max` and `min` are the larger and smaller of `a` and `sw_i` respectively.  
Example: `a = 0...011`, `sw_i = 0...0100`.   
Result: `out_o = 0...0101`.  

---

6. Compute `a * sw_i` as a sum of `sw_i` copies of `a`. Output the result to `out_o`.  
Example: `a = 5`, `sw_i = 4`. `5 * 4 == 5 + 5 + 5 + 5 = 20`.  
Result: `out_o = 0...010100`.

7. If `sw_i[1:0] == 00`, output `a` to `out_o`; if `sw_i[1:0] == 01`, output `b`; if `sw_i[1:0] == 10`, output `c`; if `sw_i[1:0] == 11`, output `d`.   
Example: `a = 0...00`, `b = 0...010`, `c = 0...011`, `d = 0...001`, `sw_i[1:0] = 01`.   
Result: `out_o = 0...010`.  

8. Compute the circumference for a given radius `sw_i`, assuming `pi = 3`. Output the result to `out_o`.   
Example: `sw_i = 0...010`.  
Result: `out_o = 0...01100`.  

9. If `sw_i` is a power of two, output `out_o = 0...01`; otherwise output `out_o = 0...0`.   
Example 1: `sw_i = 0...0100`. Result: `out_o = 0...01`.   
Example 2: `sw_i = 0...0110`. Result: `out_o = 0...00`.

10. Count the number of zeros in the binary representation of `sw_i`. Output the result to `out_o`.   
Example: `sw_i = 1...10110_0010`.   
Result: `out_o = 0...0101`.

11. Find the highest binary bit of `sw_i` whose value is `1`. If no such bit exists, output `32`. Output the result to `out_o`.   
Example: `sw_i = 0...0110`.   
Result: `out_o = 0...010`.  

12. Form a number consisting of the even-indexed binary bits of `sw_i`. Output the result to `out_o`.   
Example: `sw_i = 0...011_1011_1000`.   
Result: `out_o = 0...01_0100`.  

13. Count the number of ones in the binary representation of `sw_i` (note: `sw_i` is a signed number). Output the result to `out_o`.   
Example: `sw_i = 0...0101_0110`.   
Result: `out_o = 0...0100`.  

14. Count the number of binary bits in which `sw_i` and `a` differ. Output the result to `out_o`.   
Example: `sw_i = 0...0110`, `a = 0...01110`.   
Result: `out_o = 0...01`.  

15. Output all the one-bits of `sw_i` packed consecutively to `out_o`.   
Example: `sw_i = 0...01011011011`.   
Result: `out_o = 0...01111111`.  

16. Output to `out_o` the value of the expression: `out = (k*a + b) + c`, where `k` is `sw_i[15:12]`, `a` is `sw_i[11:8]`, `b` is `sw_i[7:4]`, `c` is `sw_i[3:0]`.  
Example: `sw_i = 0...0011_0010_0100_0011`.   
Result: `out_o = 0...01101`.   

---

17. Find the remainder of dividing `sw_i` by `a`. Output the result to `out_o`.   
Example: `sw_i = 0...0101`, `a = 0...010`.   
Result: `out_o = 0...01`.   

18. Find and output to `out_o` the number of non-overlapping occurrences of `a[2:0]` in `sw_i`.   
Example: `a[2:0] = 010`, `sw_i = 0...01101_0101`.   
Result: `out_o = 0...01`.  

19. Determine how many times the pattern `11` occurs in the binary representation of `sw_i` without overlaps. Output the result to `out_o`.   
Example: `sw_i = 0...01110`.    
Result: `out_o = 0...01`.  

20. Output to `out_o` the result of integer division `a/sw_i`.   
Example: `sw_i = 0...010`, `a = 0...0111`.   
Result: `out_o = 0...011`.  

21. Output to `out_o` the sum `sw_i[3:0]` + `sw_i[7:4]` + `sw_i[11:8]` + `sw_i[15:12]`.   
Example: `sw_i[15:0] = 0001_0010_0011_0000`.    
Result: `out_o = 0...0110`.  

22. In the number `sw_i`, replace each occurrence of `00` with `11` scanning from right to left. Output the result to `out_o`.   
Example: `sw_i = 1...101000`.    
Result: `out_o = 1...101011`.  

---

23. Swap the even-indexed bits of `sw_i` with the odd-indexed bits (i.e., swap each pair of adjacent bits). Output the result to `out_o`.   
Example: `sw_i = 0...01010_0111`.   
Result: `out_o = 0...0101_1011`.  

24. Invert the first `sw_i` bits of the number `a`. Output the result to `out_o`.   
Example: `sw_i = 0...011`, `a = 0...01010_0011`.   
Result: `out_o = 0...01010_0100`.  

25. Output the n-th term of the [Fibonacci sequence](https://ru.wikipedia.org/wiki/Числа_Фибоначчи) Fn, where n = `sw_i`. Output the result to `out_o`.   
Example: `sw_i = 0...0100`.   
Result: `out_o = 0...010`.  

26. In the number `a`, swap bits `i = sw_i[4:0]` and `j = sw_i[9:5]`. Output the result to `out_o`.   
Example: `a = 0...01001`, `sw_i[9:0] = 00000_00001`. This means bits `a[0]` and `a[1]` must be swapped.   
Result: `out_o = 0...01010`.  

---

27. Compute `a * sw_i` using addition and shift operations (long multiplication). Output the result to `out_o`.   
[Example](https://en.wikipedia.org/wiki/Binary_multiplier#Binary_long_multiplication): `a = 0...01011`, `sw_i[9:0] = 0...01110`.   
Result: `out_o = 0...010011010`.  
```  
       1011   (11 in binary)
     x 1110   (14 in binary)
     ======
       0000   (this is 1011 x 0)
      1011    (this is 1011 x 1, shifted left by 1)
     1011     (this is 1011 x 1, shifted left by 2)
  + 1011      (this is 1011 x 1, shifted left by 3)
  =========
   10011010   (154 in binary)
```

28. Output to `out_o` the n-th term of the [arithmetic progression](https://ru.wikipedia.org/wiki/Арифметическая_прогрессия) aN, where `a1 = a`, `d = sw_i[15:8]`, `n = sw_i[7:0]` (d and n are non-negative).   
Example: `sw_i[15:8] = 0000_0010`, `sw_i[7:0] = 0000_0011`, `a = 0...01`.   
Result: `out_o = 0...0101`.  

<!-- 25. *Turn on all LEDs at 50% brightness ([hint](http://wiki.amperka.ru/конспект-arduino:шим)) -->

29. Remove all occurrences of `sw_i[2:0]` from `a` with a right shift (filling in the removed areas).   
Example: `a = 0...010011010`, `sw_i[2:0] = 101`.  
Result: `out_o = 0...010010`
