# Preface

This book will guide you from the fundamentals of digital circuit design all the way to designing a single-cycle RISC-V microcontroller and writing and compiling software for it. By working through the material, you will gain practical skills in SystemVerilog, learn the basics of working with FPGAs and design tools such as Vivado, and gain hands-on experience programming in assembly language — opening the door to the world of low-level programming.

The book thus provides a unique opportunity to start from scratch and step by step master the fundamentals of processor design and FPGA development, which can serve as a first step toward a career in digital electronics.

Although the processor being built is purely academic in nature, it is perfectly capable of running simple games such as Snake. The material presented here is a collection of lab assignments completed by students at MIET as part of the "Architectures of Processor Systems" (APS) course, and is primarily aimed at those students. As a result, the text occasionally contains phrases such as "Pre-lab admission" or "Consult your instructor," which are meaningful only in a university context. If you are reading this book for self-study, most such phrases can be safely ignored.


## Motivation

The goal of the "Architectures of Processor Systems" course is to study the design and organization of processors and the systems they control. The practical component of the course focuses on developing a processor with the RISC-V architecture.

The word *Architecture* refers to a particular way of organizing something. A *processor* is a programmable device for information processing — in other words, a device whose behavior can be controlled through programs (sequences of instructions/actions). A *system* is a combination of interacting elements organized to achieve defined goals. Thus, the "Architectures of Processor Systems" discipline is concerned with the ways of organizing and building systems controlled by programmable devices.

The course is delivered by the MPSU Institute at MIET across 7 different degree programs, which vary in name and in the balance of theoretical and practical material. Despite these differences, the scope of coverage is the same across all programs, and the core subject is the same — computer organization. The programs differ only in depth and emphasis.

To engage successfully with this discipline, it is important to understand why it is relevant to you as a student in your particular field:

### Information Security

There is no doubt that people who design automotive safety systems have a thorough understanding of how those automobiles work. It is obvious that fire safety cannot be organized without understanding how materials burn or, for example, the specific characteristics of the spaces being protected. In the same way, robust information security cannot be achieved without understanding the principles of operation of the devices that receive, process, and transmit that information. For an information security specialist to enforce the rules governing the exchange and processing of information in information systems, it is clearly necessary to understand how those systems work.

Criminals in the field of information technology know how these systems are built and how they work — because the result of their actions is not "breaking" the systems (as is commonly said), but rather making them work the way the attacker wants, rather than the way the owner intends. And if catching a criminal requires thinking like a criminal, a good security professional has only one option: learn how computers work by studying the APS course.

### Computer Science and Engineering

30–40 years ago, when personal computers were still a novelty and the internet as we know it did not yet exist, the pioneers of computing predicted that in the future, electronic chips would become so cheap that they would be everywhere — in our homes, in transportation, even in the human body. At the time, this idea seemed fantastical, even absurd. Personal computers were very expensive and mostly not connected to any network. The notion that billions of tiny chips would one day be embedded in everything and cost less than a handful of seeds seemed ridiculous. Today, these ideas no longer seem far-fetched. Over the past decade, some computer or another has almost always been within arm's reach of a person. Even a metro ticket is a computer — one that was perhaps designed by a graduate of a Computer Science and Engineering program.

If you are a graduate of Computer Science and Engineering, you will most likely be developing electronics and computers in the future — digital automated devices that are typically controlled by processors and FPGAs. A typical modern electronic device consists of a set of physical sensors that send their measurements to a processor, which processes the received information according to a given program. Understanding how this works is just as reasonable as a physician knowing what organs the human body contains, even if they are not a surgeon and will not be operating. A Computer Science and Engineering graduate who understands how a computer is built will be able to develop more effective solutions: faster, more accurate, and more energy-efficient.

The logic goes: "To develop electronics, I need to understand what it is made of," "Modern electronic devices are controlled by processors" ⟹ "To develop electronics, I need to understand processors."

### Infocommunication Technologies and Communication Systems

In addition to being self-evident, there is abundant evidence that the level of civilizational development is linked to the development of communications. The design of cutting-edge communication systems and their deployment will remain one of the most pressing challenges for humanity for a long time to come. We are constantly faced with the need to connect the right parties quickly and securely. This is achieved through modern hardware-software solutions that are continuously evolving and improving. In essence, network engineers design specialized computers whose purpose is to exchange information between certain input and output nodes according to defined rules. All of this requires an understanding of the operation of programmable devices, which form the foundation of network nodes.

There are numerous diverse network processors and solutions implemented in FPGAs. Successfully participating in the development of modern networking solutions requires not only knowledge of data transmission methods, coding algorithms, and the like, but also an understanding of the operating principles of the building blocks from which network systems are constructed. The depth of such knowledge makes it possible to increase data transfer speeds and improve security.

Knowledge in the area of computer design is an essential tool in the creation of information and communication systems.

### Electronic Device Design and Technology

Not so long ago, when personal computers were just beginning to conquer the world and the internet was not yet available to everyone, many in the design and technology industry predicted a future in which electronics would be everywhere: in our homes, our transportation, and even in our own bodies. This seemed incredible and even fantastical at a time when personal computers were expensive and had no internet access.

Today, these ideas no longer seem far-fetched. In recent decades we have been constantly surrounded by electronics and numerous computing systems, some of which are brought into existence by graduates of Electronic Device Design and Technology programs. Take robots, for example. Modern robots are high-technology electronic systems designed to perform a wide range of tasks. They are equipped with sensors and processors that allow them to perceive their environment and make decisions in real time. A graduate of "Electronic Device Design and Technology" will have a unique opportunity to create and improve such devices, making them more efficient and functional.

The key point is that to succeed in a career in electronic device design and technology, one must have a deep understanding of electronic systems. This includes knowledge of how processors, sensors, and other key components work. Graduates of this program will be able to create modern electronic devices and deploy them across the most diverse application areas. Knowledge of the fundamentals of processor system organization is a powerful and essential tool in achieving the goal of creating advanced electronic systems.

### Software Engineering

For a modern software developer not to understand how a computer is structured and how it works is like a Formula 1 driver not knowing how his car works. It is simply unthinkable! It is possible, but very much the exception. Of course, a blacksmith knows how his tools work — because that knowledge allows him to use them more effectively. He understands their weaknesses and knows how to apply them cleverly in practice. Only then is the blacksmith truly valuable.

Modern programming languages make it possible to operate at a great distance from the actual hardware. Often there is practical value in this abstraction, but not always. Most modern computers are autonomous (battery-powered), which means that efficiency directly translates to battery life. Understanding the nuances can lead to significant energy savings. Sometimes you need to choose hardware for a server, or figure out why obviously fast code is running slowly. You frequently have to get up to speed with new technologies, frameworks, languages, services, and libraries — but all of this comes easily only when there is a solid foundation that answers the question: "How does this work, and why does it work this way?" Knowledge of APS helps with all of the above.

"Understanding how a computer works" does not mean "building (designing) a computer." Doctors know how the human body is structured in order to treat it, not to design it. Racing drivers know their cars in order to optimize and fully exploit them. Likewise, a software developer needs to understand how a computer works not in order to design processors, but to use the computer more effectively and intelligently.

### Applied Mathematics

Virtually all modern applications of mathematics are connected in one way or another with computers: big data, artificial intelligence, robotics, finance, and so on. Mathematics has long since outgrown the pages of a notebook — today, algorithms are the thoughts of processors.

Mathematical applications, whatever form they take — simulation, automation, computation, or something else — require an instrument to execute them: a computer. Understanding how your primary instrument is structured and how it works provides a clear advantage over those who lack that understanding. Sometimes you need to choose hardware for a system solving a particular problem; sometimes you need to figure out why obviously fast code is running slowly. You frequently have to get up to speed with new technologies, frameworks, languages, services, and libraries — but all of this comes easily only when there is a solid foundation that answers the question: "How does this work, and why does it work this way?" Knowledge of APS helps with all of the above.

"Understanding how a computer works" does not mean "building (designing) a computer." Doctors know how the human body is structured in order to treat it, not to design it. Racing drivers know their cars in order to optimize and fully exploit them. Likewise, an applied mathematics graduate needs to understand how a computer works not in order to design processors, but to use the computer more effectively and intelligently in their own applications.

### Radio Engineering

The use of radio waves today helps solve an enormous range of problems related to transmitting information and energy over a distance, locating and positioning objects, studying the properties of reflecting objects, and much more — limited only by one's imagination. In practice, radio waves turn out to be remarkably useful, and antennas are the devices used to control them and extract maximum value from them. These devices can be quite complex, and professionals capable of designing them are needed behind them. The devices that control, monitor, and receive information from antennas are specialized systems that ultimately convert radio signals into electrical digital signals, or vice versa.

Modern microwave integrated circuits (operating at extremely high frequencies), used in antenna systems, are frequently programmable. This means they either contain a processor or are designed to interact with processors. To unlock the full potential of these chips, you need to know how processors work. Understanding their functions is also valuable in radio engineering, especially when you need to control signals within strict timing constraints.

Radio engineering is not just about working with radio signals, but also about processing them. Sometimes signals must be processed very quickly. In such cases it is important to know which computing device to choose to ensure processing accuracy within the required time constraints while staying within power consumption requirements. Without an understanding of APS you cannot solve such problems — because you have to choose from a wide range of devices, including microcontrollers, digital signal processors with various characteristics, and FPGAs. But how can you make that choice if you do not even understand what these things are?

In essence, a radio engineer is a specialist who can not only calculate an antenna design, but also build it and develop systems for control, data acquisition, and processing — using the knowledge gained from APS.

Radio engineering is tied to radio signals, and radio signals in modern equipment are always tied to processors. If you want to be at the forefront of this exciting field, studying APS is an important step on that path.

## How to Read This Book

The book is designed for a wide range of readers with varying levels of preparation at the start of the APS course, so some material may be redundant for some readers while being essential for others.

Regardless of your background, it is recommended to begin by reading the documents in the "Introduction" section.

You can then proceed to the "Lab Assignments" section. Before each lab session, you are **strongly encouraged** to read the corresponding lab guide in advance, as the guides are quite detailed and require some time to read. The time allocated for the lab session itself should be used to maximum effect: carrying out practical work, consulting with your instructor, debugging the device blocks you have designed, and so on — all of which requires having read the guide beforehand.

It is also important to note that at the beginning of many lab assignments, **additional preparation materials** are listed, with references to chapters in the "Basic SystemVerilog Constructs" section that the student **must study** before completing that lab. This section is primarily aimed at students who have not previously worked with Verilog/SystemVerilog; however, even if you have experience with these languages, it is recommended to skim through those chapters and test your knowledge in the "Check Yourself" section.

Lab sessions will use the `Vivado` EDA tool (along with `Nexys A7` development boards). This is a very complex professional tool that can take years to master fully. During this lab course there is no time for years of Vivado study, so the essential information for working with the tool has been compiled for you in the "Vivado Basics" section. This information is sufficient to complete the entire lab cycle using `Vivado`.

Traditionally, these lab assignments are considered challenging. However, over the years of refining the guides with students, numerous supplementary materials, clarifications, and notes highlighting potential pitfalls have been added. At this point, successfully completing a lab assignment requires only that the student read the provided material carefully and not be afraid to ask a question if something is unclear.

If you are reading this book outside the APS course, you are free to choose your own software tools and debugging approaches. The [repository](https://github.com/MPSU/APS) accompanying this book will contain some files specific to Nexys A7 boards (so-called _constraints_), but with the appropriate level of skill you will easily be able to port them to your own board. In that case, the authors would appreciate it if you could contribute the resulting files along with the board name, so they can be added to a separate folder for other boards for the benefit of future readers. For any questions, comments, or suggestions, you can contact the course authors through the `Issues` and `Discussions` sections of the repository.

This book can also be useful and interesting for readers who do not have any development board: functionality is verified primarily through simulation, i.e., in software (in fact, 90% of the time you will be testing everything through simulation).

In the course of completing the lab assignments, you will inevitably encounter both errors related to Vivado's operation and errors in your SystemVerilog code. The first recommendation is always to read the error message carefully. For SystemVerilog-related errors, the message most often contains all the information needed to resolve the issue. If the message is unclear, consult the [list of common errors](Other/FAQ.md).

The material in this book contains many links, which in the electronic version are of course clickable. However, if you have the pleasure of reading this book in "analog" format, all links are provided as footnotes on the corresponding page in plain text. Plain text was chosen over QR codes to allow links to be typed in manually (all links are in Unicode format, so do not worry about having to type something like "https://ru.wikipedia.org/wiki/%D0%A2%D1%80%D0%B8%D0%B3%D0%B3%D0%B5%D1%80"). Furthermore, the smart cameras on modern smartphones handle text link recognition very well, so the authors hope that the absence of QR codes will not cause inconvenience in that regard either.

The majority of the information concerning the RISC-V architecture is taken directly from the specification. Since work on the specification is still ongoing (although the base rv32i instruction set is now frozen and will not change), all references to specific pages of the specification will point to the following versions of two documents:

- "The RISC-V Instruction Set Manual Volume I: Unprivileged ISA" — [document version `20240411`](https://github.com/riscv/riscv-isa-manual/releases/download/20240411/unpriv-isa-asciidoc.pdf);
- "The RISC-V Instruction Set Manual Volume II: Privileged Architecture" — [document version `20240411`](https://github.com/riscv/riscv-isa-manual/releases/download/20240411/priv-isa-asciidoc.pdf).

The lab course is inseparably linked to the online repository located at: https://github.com/MPSU/APS. This repository contains the course materials, verification environment, ready-made modules, and constraint files for the Nexys A7 development board.

For any questions, comments, or suggestions, you can contact the course authors through the Issues and Discussions sections of this repository.

This course has evolved continuously over several years up until its publication. The authors acknowledge that some imperfections may remain in the text that can no longer be corrected after printing. To allow readers to learn about errors discovered after publication, a dedicated errata document is located at the root of the repository.

## How to Use the Repository

The root of the repository contains the following items (folders are marked with a trailing '/'):

- <p style="color:LightGray;">.github/</p>
- <p style="color:LightGray;">.pic/</p>
- Basic Verilog structures/
- Introduction/
- Labs/
- <p style="color:LightGray;">Lectures/</p>
- Other/
- Vivado Basics/
- <p style="color:LightGray;">.gitmodules</p>
- <p style="color:LightGray;">LICENSE</p>
- <p style="color:LightGray;">README.md</p>

Items shown in gray are not needed when completing the lab assignments.

The Introduction, Basic Verilog structures, and Vivado Basics folders contain the material corresponding to Parts 1, 3, and 4 of this book, respectively. The Other folder contains, among other things, the material that forms Part 5 of this book.

The structure of the Labs folder is as follows:

01. Adder/
02. Arithmetic-logic unit/
03. Register file and memory/
04. Primitive programmable device/
05. Main decoder/
06. Main memory/
07. Datapath/
08. Load-store unit/
09. LSU Integration/
10. Interrupt subsystem/
11. Interrupt integration/
12. Daisy chain/
13. Peripheral units/
14. Programming/
15. Programming device/
16. Coremark/
Made-up modules/
Readme.md

Each of these folders contains the instructional materials for the corresponding lab assignment.

In almost every such folder there is a file named _lab_xx.tb_xxx.sv_ — this is the verification environment (testbench) file for that lab assignment. This file must be added to the _Simulation Sources_ of the project (see the _Vivado Basics_ section for details).

Additionally, a lab folder may contain _xxx_pkg.sv_ and _xxx.mem_ files, holding parameters and data, respectively, that are used to initialize the device memory. These files must be added to the _Design Sources_ of the project.

Most folders also contain a _board files_ subfolder. This subfolder contains the top-level module (if required), a description of how to interact with it, and constraint files for the _Nexys A7_ development board.

Furthermore, the `Made-up modules/` folder contains pre-built modules for certain lab assignments. If for any reason you were unable to complete a lab assignment, you can continue working through the course by using the corresponding ready-made module from this folder.

The repository has a mirror located at: https://gitlab.chips-miet.ru/MPSU/APS. The file structure of the mirror is identical to the original repository.

## Course History and Contributors

Disciplines related to computer organization have been taught at MIET since its founding. The current course evolved from "Microprocessor Means and Systems" (MMS), taught to the MPiTK (Microdevices and Technical Cybernetics) faculty — first by [Yuri Vasilyevich Savchenko](https://miet.ru/person/10551), and later by [Alexei Leonidovich Pereverzev](https://miet.ru/person/49309). From 2014 to 2022, the course was conducted and significantly modernized by [Mikhail Gennadyevich Popov](https://miet.ru/person/50480) together with a team of staff and students from the MPSU Institute. Since 2022, the course for the IB, IKT, KT, and RT student groups has been taught by [Alexander Mikhailovich Silantyev](https://miet.ru/person/64030), while the IVT, PIN, and PM groups are taught by [Alexander Nikolaevich Orlov](https://miet.ru/person/53686); the development of course materials has been taken over by [Andrei Pavlovich Solodovnikov](https://miet.ru/person/141139).

Between 2019 and 2023 the theoretical part of the course was substantially revised, modernized, and expanded. During the same period, the lab assignments were redesigned and fully updated to use the RISC-V architecture, and new methods for assessing student knowledge were introduced. All course materials, including [lecture recordings](https://www.youtube.com/c/АПСПопов), were made publicly available.

The primary influences on the structure and content of the course in its current form are: the original MMS lectures for MPiTK, the 6.004 Computation Structures course taught at MIT, Harris & Harris "Digital Design and Computer Architecture," and Orlov & Tsil'ker "Computer Organization and Systems."

The following current and former students and staff of the MPSU Institute helped prepare the course and repository: <!--- In alphabetical order -->

|     Full Name                                                |                                                           Contribution to the course                                                                                                                                  |
|-------------------------------------------------------------|----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------|
| Barkov Evgeny Sergeyevich                                   | Professional consultations on SystemVerilog language details, the RISC-V specification, RTL development, synthesis, and constraints.                                                                     |
| Bulavin Nikita Sergeyevich                                  | Refinement of materials, preparation of testbenches and top-level modules for Nexys A7 boards for the lab assignments.                                                                                   |
| Kozin Alexei Alexandrovich                                  | Refinement of materials, preparation of obfuscated modules for the lab assignments.                                                                                                                      |
| [Kuleshov Vladislav Konstantinovich](https://t.me/SaintLiver) | Proofreading and correction of errors in the course materials, collection of student feedback.                                                                                                          |
| Orlov Alexander Nikolaevich                                 | Professional consultations on SystemVerilog language details, the RISC-V specification, RTL development, and example programs illustrating architectural features.                                       |
| Primakov Evgeny Vladimirovich                               | Professional consultations on SystemVerilog language details, the RISC-V specification, RTL development, and microarchitecture topics.                                                                   |
| [Protasova Ekaterina Andreyevna](https://t.me/Katkus_s)     | Preparation of individual assignments and pre-lab admission tasks, proofreading and refinement of materials, collection of student feedback.                                                             |
| Rusanovsky Bogdan Vitalyevich                               | Migration of the interrupt lab assignment from PDF to Markdown, preparation of illustrations.                                                                                                            |
| Ryzhkova Darya Vasilyevna                                   | Preparation of testbenches for the lab assignments.                                                                                                                                                      |
| Silantyev Alexander Mikhailovich                            | Professional consultations on SystemVerilog language details, the RISC-V specification, RTL development, microarchitecture topics, synthesis and constraints, and compilation and profiling specifics.   |
| Strelkov Daniil Vladimirovich                               | Refinement of materials, preparation of testbenches for the lab assignments, and preparation of course structure illustrations.                                                                          |
| [Ternovoy Nikolai Eduardovich](https://t.me/cpu_design)     | Professional consultations on SystemVerilog language details, the RISC-V specification, RTL development, proofreading of materials, collection of student feedback.                                      |
| Kharlamov Alexander Alexandrovich                           | Refinement of materials, design of auxiliary modules for the lab assignments.                                                                                                                            |
| [Khisamov Vasil Tagirovich](https://t.me/PascalVT)          | Proofreading of materials, collection of student feedback.                                                                                                                                               |
| Chusov Sergei Andreyevich                                   | Proofreading of materials, collection of student feedback.                                                                                                                                               |

In addition, some of the illustrations were drawn by Ekaterina Alexandrovna Krasnyuk.

With that, the introductory remarks are complete — I wish you success on this most fascinating journey!
