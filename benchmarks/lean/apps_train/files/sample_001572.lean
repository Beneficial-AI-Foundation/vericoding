Story:
In the realm of numbers, the apocalypse has arrived. Hordes of zombie numbers have infiltrated and are ready to turn everything into undead. The properties of zombies are truly apocalyptic: they reproduce themselves unlimitedly and freely interact with each other. Anyone who equals them is doomed. Out of an infinite number of natural numbers, only a few remain. This world needs a hero who leads remaining numbers in hope for survival: The highest number to lead those who still remain.

Briefing:
There is a list of positive natural numbers. Find the largest number that cannot be represented as the sum of this numbers, given that each number can be added unlimited times. Return this number, either 0 if there are no such numbers, or -1 if there are an infinite number of them.

Example:
```
Let's say [3,4] are given numbers. Lets check each number one by one:
1 - (no solution) - good
2 - (no solution) - good
3 = 3 won't go
4 = 4 won't go
5 - (no solution) - good
6 = 3+3 won't go
7 = 3+4 won't go
8 = 4+4 won't go
9 = 3+3+3 won't go
10 = 3+3+4 won't go
11 = 3+4+4 won't go
13 = 3+3+3+4 won't go
```
...and so on. So 5 is the biggest 'good'. return 5

Test specs:
Random cases will input up to 10 numbers with up to 1000 value

Special thanks:
Thanks to Voile-sama, mathsisfun-sama, and Avanta-sama for heavy assistance. And to everyone who tried and beaten the kata ^_^

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded