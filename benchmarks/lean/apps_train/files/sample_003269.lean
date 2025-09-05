A system is transmitting messages in binary, however it is not a perfect transmission, and sometimes errors will occur which result in a single bit flipping from 0 to 1, or from 1 to 0.

To resolve this, A 2-dimensional Parity Bit Code is used: https://en.wikipedia.org/wiki/Multidimensional_parity-check_code

In this system, a message is arrayed out on a M x N grid. A 24-bit message could be put on a 4x6 grid like so:

>1 0 1 0 0 1
>1 0 0 1 0 0
>0 1 1 1 0 1
>1 0 0 0 0 1

Then, Parity bits are computed for each row and for each column, equal to 1 if there is an odd number of 1s in the row of column, and 0 if it is an even number. The result for the above message looks like:

>1 0 1 0 0 1 1
>1 0 0 1 0 0 0
>0 1 1 1 0 1 0
>1 0 0 0 0 1 0
>1 1 0 0 0 1

Since the 1st row, and 1st, 2nd and 6th column each have an odd number of 1s in them, and the others all do not.

Then the whole message is sent, including the parity bits. This is arranged as:

> message + row_parities + column_parities
> 101001100100011101100001 + 1000 + 110001
> 1010011001000111011000011000110001

If an error occurs in transmission, the parity bit for a column and row will be incorrect, which can be used to identify and correct the error. If a row parity bit is incorrect, but all column bits are correct, then we can assume the row parity bit was the one flipped, and likewise if a column is wrong but all rows are correct.

 Your Task: 

Create a function correct, which takes in integers M and N, and a string of bits where the first M\*N represent the content of the message, the next M represent the parity bits for the rows, and the final N represent the parity bits for the columns. A single-bit error may or may not have appeared in the bit array.

The function should check to see if there is a single-bit error in the coded message, correct it if it exists, and return the corrected string of bits.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
