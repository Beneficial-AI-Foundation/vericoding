Petr likes to come up with problems about randomly generated data. This time problem is about random permutation. He decided to generate a random permutation this way: he takes identity permutation of numbers from $1$ to $n$ and then $3n$ times takes a random pair of different elements and swaps them. Alex envies Petr and tries to imitate him in all kind of things. Alex has also come up with a problem about random permutation. He generates a random permutation just like Petr but swaps elements $7n+1$ times instead of $3n$ times. Because it is more random, OK?!

You somehow get a test from one of these problems and now you want to know from which one.

-----Input-----

In the first line of input there is one integer $n$ ($10^{3} \le n \le 10^{6}$).

In the second line there are $n$ distinct integers between $1$ and $n$ — the permutation of size $n$ from the test.

It is guaranteed that all tests except for sample are generated this way: First we choose $n$ — the size of the permutation. Then we randomly choose a method to generate a permutation — the one of Petr or the one of Alex. Then we generate a permutation using chosen method.

-----Output-----

If the test is generated via Petr's method print "Petr" (without quotes). If the test is generated via Alex's method print "Um_nik" (without quotes).

-----Example-----
Input
5
2 4 5 1 3

Output
Petr

-----Note-----

Please note that the sample is not a valid test (because of limitations for $n$) and is given only to illustrate input/output format. Your program still has to print correct answer to this test to get AC.

Due to randomness of input hacks in this problem are forbidden.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded
