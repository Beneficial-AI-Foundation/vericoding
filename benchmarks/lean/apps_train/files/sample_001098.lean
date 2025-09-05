Chef Ada is the FootBall coach of the Dinosaurs Institute of Technology.
There are $N$ dinosaurs (enumerated $1$ through $N$) placed in a line. The i-th dinosaur has a height of $i$ meters.
Ada is training The dinosaurs in the following tactic:
- Initially the leftmost dinosaur has the ball.
- The dinosaur that has the ball passes the ball to the nearest dinosaur to the right that is tallest than him.
- The previous step continues until the ball reaches the tallest dinosaur, then he throws the ball and scores a goal!
Help Ada reordering the dinosaurs in such a way that the ball is passed from dinosaur to dinosaur exactly $K$ times.
For example, if there are $5$ dinosaurs ordered as $[2,3,1,5,4]$, then the ball goes $2 \rightarrow 3\rightarrow5 \rightarrow goal$, and the ball was passed two times.

-----Input:-----
- First line will contain $T$, number of testcases.
- Each test case consist of a line with two space separated integers $N,K$.

-----Output:-----
For each testcase, output in a single line conaining $N$ integers representing one possible ordering in which the dinosaurs can be placed.

-----Constraints-----
- $1 \leq T \leq 2^8$
- $2 \leq N \leq 20$
- $0 \leq K \leq N-1$

-----Sample Input:-----
1
5 2

-----Sample Output:-----
2 3 1 5 4

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded_and_plausible