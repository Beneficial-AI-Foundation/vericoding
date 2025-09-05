In 17th century our Chef was a Wizard. He asked his small son "Anshu" to bring him the secret of the Magical Mountain. The boy after travelling a lot reached the Mountain.

The description of the Mountain was as follows:
- Mountain contains N magical stones. Each of them has a unique number.
- Mountain was divided into many levels, where at ith level atmost 2^i stones can be found.
- Between stones there exist a magical path containing lava.
- A stone can be connected with maximum of three stones.
- Peak of the mountain contains stone with number 1.
- If Stone 1 is first connected to stone 2 and then to 3. Assume 2 is to the left of 3.

Now, to get the secret of the mountain, Anshu started climbing from the left. On the way he used his magical wand to protect him from lava. But, while climbing he came to know that he is able to see only the one stone at each level. After reaching the peak he slided down and did the the same process. These stones that he saw shows the secret of the mountain, if they are placed in a non decreasing order on a sunny day. Anshu doesn't remember the stones number that he saw. Help him in recollecting them and getting the secret to his father.

The mountain looks like this

-----Input-----
- First line contains T the number of test cases.
- First line of each test test case contains N.
- Next N-1 lines contains X and Y the stones which are connected.

-----Output-----
- Output the required non decreasing sequence.

-----Constraints and Subtasks-----
- 1 <= T <= 10
- 1 <= X, Y <= N
Subtask 1: 20 points
- 3<=N<=100
Subtask 2: 30 points
- 3<=N<=10000
Subtask 3: 50 points
- 3<=N<=100000

-----Example-----
Input:
1
5
1 2
1 3
2 4
2 5

Output:
1 2 3 4 5

def find_mountain_secret (n : Nat) (edges : List (Nat × Nat)) : String := sorry

def parseNums (s : String) : List Nat :=
  (s.split (· = ' ')).filterMap String.toNat?

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded