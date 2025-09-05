Everybody seems to think that the Martians are green, but it turns out they are metallic pink and fat. Ajs has two bags of distinct nonnegative integers. The bags are disjoint, and the union of the sets of numbers in the bags is $\{0,1,…,M-1\}$, for some positive integer $M$. Ajs draws a number from the first bag and a number from the second bag, and then sums them modulo $M$.

What are the residues modulo $M$ that Ajs cannot obtain with this action?

-----Input-----

The first line contains two positive integer $N$ ($1 \leq N \leq 200\,000$) and $M$ ($N+1 \leq M \leq 10^{9}$), denoting the number of the elements in the first bag and the modulus, respectively.

The second line contains $N$ nonnegative integers $a_1,a_2,\ldots,a_N$ ($0 \leq a_1<a_2< \ldots< a_N<M$), the contents of the first bag.

-----Output-----

In the first line, output the cardinality $K$ of the set of residues modulo $M$ which Ajs cannot obtain.

In the second line of the output, print $K$ space-separated integers greater or equal than zero and less than $M$, which represent the residues Ajs cannot obtain. The outputs should be sorted in increasing order of magnitude. If $K$=0, do not output the second line.

-----Examples-----
Input
2 5
3 4

Output
1
2

Input
4 1000000000
5 25 125 625

Output
0

Input
2 4
1 3

Output
2
0 2

-----Note-----

In the first sample, the first bag and the second bag contain $\{3,4\}$ and $\{0,1,2\}$, respectively. Ajs can obtain every residue modulo $5$ except the residue $2$: $ 4+1 \equiv 0, \, 4+2 \equiv 1, \, 3+0 \equiv 3, \, 3+1 \equiv 4 $ modulo $5$. One can check that there is no choice of elements from the first and the second bag which sum to $2$ modulo $5$.

In the second sample, the contents of the first bag are $\{5,25,125,625\}$, while the second bag contains all other nonnegative integers with at most $9$ decimal digits. Every residue modulo $1\,000\,000\,000$ can be obtained as a sum of an element in the first bag and an element in the second bag.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: guarded