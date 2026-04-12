# Approximate Vector Length Computation Module

The `vector_abs` module is designed to compute the approximate length of a vector in Euclidean space (i.e., the expression `sqrt(a^2+b^2)`). To make efficient use of logic gates, the following approximation is applied:

`sqrt(a^2+b^2) ≈ max + min/2`, where max and min are the larger and smaller of the two numbers, respectively [**Richard Lyons: Understanding Digital Signal Processing, Chapter 13.2, p. 475**].

The `max_min` module is used to determine the maximum/minimum values, and the `half_divider` module is used to compute the division by two.
