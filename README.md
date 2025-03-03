This repository is a supplement to the article

# **Static Communicaton Analysis for Hardware Design**

_Mads Rosendahl and Maja H. Kirkeby

Roskilde University
Computer Science
Denmark_
madsr@ruc.dk, kirkebym@acm.org

Hardware acceleration of algorithms is an effective method for improving performance 
in high-demand computational tasks.
However, developing hardware designs for such acceleration fundamentally differs 
from software development, as it requires a deep understanding of the highly 
parallel nature of the hardware architecture.
In this paper, we present a framework for the static analysis of communication 
within datapath architectures designed for field-programmable gate arrays (FPGAs).
Our framework aims to enhance hardware design and optimization by providing 
insights into communication patterns within the architecture, which are essential for ensuring efficient data handling.
We also explore various techniques to balance efficiency and precision in the analysis, considering the trade-offs between computational overhead and the approximation of possible results.

-----------------

This repository contains implementations of the semantics and analysis of a subset of the hardware description language Chisel.
The implementation is written in Java 19+ and is converted from an earlier version in Scala.
It uses the newer features with records, pattern matching in switch statements and lamnda expressions.
It is an experiment to examine how easy it is to express semantics and analysis in java.
The current version is quite similar to how it could be written in ML or Scala.

The directory 'in' contains examples of programs in textual form. 
The Parser converts programs into abstract syntax using 
data types (records) in the file AbsSyn. 
The PrettyPrinter can revert abstract syntax back to textual form.

-----------------

The file 'Chisel.java' can convert the abstract syntax into the Chisel syntax.
The converted Chisel programs from the abstract syntax can be found in the directory 'chisel'.
The file 'Interpreter.java' contains the standard interpretation of the Chisel programs.
