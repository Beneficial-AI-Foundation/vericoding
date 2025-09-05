Coffee Vending Machine Problems [Part 1]

You have a vending machine, but it can not give the change back. You decide to implement this functionality. First of all, you need to know the minimum number of coins for this operation (i'm sure you don't want to return 100 pennys instead of 1$ coin).
So, find an optimal number of coins required, if you have unlimited set of coins with given denominations.

Assume all inputs are valid positive integers, and every set of coin denominations has len 4 for simplicity;

Examples:

optimal_number_of_coins(1, [1, 2, 5, 10]) 
(1 penny) so returns 1  
optimal_number_of_coins(5, [1, 2, 5, 10])
(5) so returns 1
optimal_number_of_coins(6, [1, 3, 5, 10])
(3+3 or 5+1) = 6 so returns 2
optimal_number_of_coins(10, [1, 2, 5, 10]) 
(10) so returns 1
optimal_number_of_coins(12, [1, 3, 5, 10])
(10+1+1) = 12 so returns 3
optimal_number_of_coins(53, [1, 2, 5, 25])
(25+25+2+1) = 53 so returns 4
optimal_number_of_coins(7, [1, 1, 1, 25])
(1+1+1+1+1+1+1) = 7 so returns 7
etc..

Have fun =)

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded
