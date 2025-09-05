You are an all-powerful being and you have created a rectangular world. In fact, your world is so bland that it could be represented by a $r \times c$ grid. Each cell on the grid represents a country. Each country has a dominant religion. There are only two religions in your world. One of the religions is called Beingawesomeism, who do good for the sake of being good. The other religion is called Pushingittoofarism, who do murders for the sake of being bad.

Oh, and you are actually not really all-powerful. You just have one power, which you can use infinitely many times! Your power involves missionary groups. When a missionary group of a certain country, say $a$, passes by another country $b$, they change the dominant religion of country $b$ to the dominant religion of country $a$.

In particular, a single use of your power is this:   You choose a horizontal $1 \times x$ subgrid or a vertical $x \times 1$ subgrid. That value of $x$ is up to you;  You choose a direction $d$. If you chose a horizontal subgrid, your choices will either be NORTH or SOUTH. If you choose a vertical subgrid, your choices will either be EAST or WEST;  You choose the number $s$ of steps;  You command each country in the subgrid to send a missionary group that will travel $s$ steps towards direction $d$. In each step, they will visit (and in effect convert the dominant religion of) all $s$ countries they pass through, as detailed above.  The parameters $x$, $d$, $s$ must be chosen in such a way that any of the missionary groups won't leave the grid. 

The following image illustrates one possible single usage of your power. Here, A represents a country with dominant religion Beingawesomeism and P represents a country with dominant religion Pushingittoofarism. Here, we've chosen a $1 \times 4$ subgrid, the direction NORTH, and $s = 2$ steps.  [Image] 

You are a being which believes in free will, for the most part. However, you just really want to stop receiving murders that are attributed to your name. Hence, you decide to use your powers and try to make Beingawesomeism the dominant religion in every country.

What is the minimum number of usages of your power needed to convert everyone to Beingawesomeism?

With god, nothing is impossible. But maybe you're not god? If it is impossible to make Beingawesomeism the dominant religion in all countries, you must also admit your mortality and say so.

-----Input-----

The first line of input contains a single integer $t$ ($1 \le t \le 2\cdot 10^4$) denoting the number of test cases.

The first line of each test case contains two space-separated integers $r$ and $c$ denoting the dimensions of the grid ($1 \le r, c \le 60$). The next $r$ lines each contains $c$ characters describing the dominant religions in the countries. In particular, the $j$-th character in the $i$-th line describes the dominant religion in the country at the cell with row $i$ and column $j$, where:  "A" means that the dominant religion is Beingawesomeism;  "P" means that the dominant religion is Pushingittoofarism. 

It is guaranteed that the grid will only contain "A" or "P" characters. It is guaranteed that the sum of the $r \cdot c$ in a single file is at most $3 \cdot 10^6$.

-----Output-----

For each test case, output a single line containing the minimum number of usages of your power needed to convert everyone to Beingawesomeism, or the string "MORTAL" (without quotes) if it is impossible to do so. 

-----Example-----
Input
4
7 8
AAPAAAAA
PPPPAAAA
PPPPAAAA
APAAPPPP
APAPPAPP
AAAAPPAP
AAAAPPAA
6 5
AAAAA
AAAAA
AAPAA
AAPAP
AAAPP
AAAPP
4 4
PPPP
PPPP
PPPP
PPPP
3 4
PPPP
PAAP
PPPP

Output
2
1
MORTAL
4

-----Note-----

In the first test case, it can be done in two usages, as follows:

Usage 1: [Image] 

Usage 2: [Image] 

In the second test case, it can be done with just one usage of the power. 

In the third test case, it is impossible to convert everyone to Beingawesomeism, so the answer is "MORTAL".

def solve_religion_grid (r c : Nat) (grid : Grid) : Answer := sorry

theorem output_format (r c : Nat) (grid : Grid) :
  let result := solve_religion_grid r c grid
  result = "0" ∨ result = "1" ∨ result = "2" ∨ result = "3" ∨ result = "4" ∨ result = "MORTAL" :=
sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded
