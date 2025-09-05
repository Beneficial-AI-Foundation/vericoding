Yeah, we failed to make up a New Year legend for this problem.

A permutation of length $n$ is an array of $n$ integers such that every integer from $1$ to $n$ appears in it exactly once. 

An element $y$ of permutation $p$ is reachable from element $x$ if $x = y$, or $p_x = y$, or $p_{p_x} = y$, and so on. 

The decomposition of a permutation $p$ is defined as follows: firstly, we have a permutation $p$, all elements of which are not marked, and an empty list $l$. Then we do the following: while there is at least one not marked element in $p$, we find the leftmost such element, list all elements that are reachable from it in the order they appear in $p$, mark all of these elements, then cyclically shift the list of those elements so that the maximum appears at the first position, and add this list as an element of $l$. After all elements are marked, $l$ is the result of this decomposition.

For example, if we want to build a decomposition of $p = [5, 4, 2, 3, 1, 7, 8, 6]$, we do the following:  initially $p = [5, 4, 2, 3, 1, 7, 8, 6]$ (bold elements are marked), $l = []$;  the leftmost unmarked element is $5$; $5$ and $1$ are reachable from it, so the list we want to shift is $[5, 1]$; there is no need to shift it, since maximum is already the first element;  $p = [\textbf{5}, 4, 2, 3, \textbf{1}, 7, 8, 6]$, $l = [[5, 1]]$;  the leftmost unmarked element is $4$, the list of reachable elements is $[4, 2, 3]$; the maximum is already the first element, so there's no need to shift it;  $p = [\textbf{5}, \textbf{4}, \textbf{2}, \textbf{3}, \textbf{1}, 7, 8, 6]$, $l = [[5, 1], [4, 2, 3]]$;  the leftmost unmarked element is $7$, the list of reachable elements is $[7, 8, 6]$; we have to shift it, so it becomes $[8, 6, 7]$;  $p = [\textbf{5}, \textbf{4}, \textbf{2}, \textbf{3}, \textbf{1}, \textbf{7}, \textbf{8}, \textbf{6}]$, $l = [[5, 1], [4, 2, 3], [8, 6, 7]]$;  all elements are marked, so $[[5, 1], [4, 2, 3], [8, 6, 7]]$ is the result. 

The New Year transformation of a permutation is defined as follows: we build the decomposition of this permutation; then we sort all lists in decomposition in ascending order of the first elements (we don't swap the elements in these lists, only the lists themselves); then we concatenate the lists into one list which becomes a new permutation. For example, the New Year transformation of $p = [5, 4, 2, 3, 1, 7, 8, 6]$ is built as follows:  the decomposition is $[[5, 1], [4, 2, 3], [8, 6, 7]]$;  after sorting the decomposition, it becomes $[[4, 2, 3], [5, 1], [8, 6, 7]]$;  $[4, 2, 3, 5, 1, 8, 6, 7]$ is the result of the transformation. 

We call a permutation good if the result of its transformation is the same as the permutation itself. For example, $[4, 3, 1, 2, 8, 5, 6, 7]$ is a good permutation; and $[5, 4, 2, 3, 1, 7, 8, 6]$ is bad, since the result of transformation is $[4, 2, 3, 5, 1, 8, 6, 7]$.

Your task is the following: given $n$ and $k$, find the $k$-th (lexicographically) good permutation of length $n$.

-----Input-----

The first line contains one integer $t$ ($1 \le t \le 1000$) — the number of test cases.

Then the test cases follow. Each test case is represented by one line containing two integers $n$ and $k$ ($1 \le n \le 50$, $1 \le k \le 10^{18}$).

-----Output-----

For each test case, print the answer to it as follows: if the number of good permutations of length $n$ is less than $k$, print one integer $-1$; otherwise, print the $k$-th good permutation on $n$ elements (in lexicographical order).

-----Example-----
Input
5
3 3
5 15
4 13
6 8
4 2

Output
2 1 3 
3 1 2 5 4 
-1
1 2 6 3 4 5 
1 2 4 3

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
