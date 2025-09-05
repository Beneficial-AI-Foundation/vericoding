The Government of Siruseri is no different from any other when it comes to being "capital-centric" in its policies. Recently the government decided to set up a nationwide fiber-optic network to take Siruseri into the digital age. And as usual, this decision was implemented in a capital centric manner --- from each city in the country, a fiber optic cable was laid to the capital! Thus, traffic between any two cities had to go through the capital.
Soon, it became apparent that this was not quite a clever idea, since any breakdown at the capital resulted in the disconnection of services between other cities. So, in the second phase, the government plans to connect a few more pairs of cities directly by fiber-optic cables. The government has specified that this is to be done in such a way that the disruption of services at any one city will still leave the rest of the country connected.
The government has data on the cost of laying fiber optic cables between every pair of cities. You task is to compute the minimum cost of additional cabling required to ensure the requirement described above is met.
For example, if Siruseri has $4$ cities numbered $1,2,3$ and $4$ where $1$ is the capital and further suppose that the cost of laying cables between these cities are as given in the table below:

Note that the government has already connected the capital with every other city. So, if we connect the cities $2$ and $3$ as well as $3$ and $4$, you can check that disruption of service at any one city will still leave the other cities connected. The cost of connecting these two pairs is $4 + 6 = 10$. The same effect could have been achieved by connecting $2$ and $3$ as well as $2$ and $4$, which would have cost $4 + 5 = 9$. You can check that this is the best you can do.
Your task is to write a program that allows the government to determine the minimum cost it has to incur in laying additional cables to fulfil the requirement.

-----Input:-----
- The first line of the input contains a single integer $N$ indicating the number of cities in Siruseri. You may assume that the capital city is always numbered $1$. 
- This is followed by $N$ lines of input each containing $N$ integers. 
- The $j^{th}$ integer on line $i$ is the cost of connecting city $i$ with city $j$. The $j^{th}$ integer on line $i$ will be the same as the $i^{th}$ integer on line $j$ (since the links are bidirectional) and the $i^{th}$ entry on line $i$ will always be $0$ (there is no cost in connecting a city with itself).

-----Output:-----
A single integer indicating the minimum total cost of the links to be added to ensure that disruption of services at one city does not disconnect the rest of the cities.

-----Constraints:-----
- $1 \leq N \leq 2000$.
- $0 \leq$ costs given in the input $\leq 100000$

-----Sample Input-----
4
0 7 8 10
7 0 4 5 
8 4 0 6
10 5 6 0

-----Sample Output-----
9

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded