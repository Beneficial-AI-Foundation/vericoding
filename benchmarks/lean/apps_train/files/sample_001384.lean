Indraneel's student has given him data from two sets of experiments that the student has performed. Indraneel wants to establish a correlation between the two sets of data. Each data set is a sequence of $N$ numbers. The two data sets do not match number for number, but Indraneel believes that this is because data has been shifted due to inexact tuning of the equipment.
For example, consider the following two sequences:
$ $
3  8   4  23  9  11  28
2  3  22  26  8  16  12

$ $
Indraneel observes that if we consider the subsequences $3,4,23,9$ and $2,3,22,8$ and examine their successive differences we get $1,19,-14$. He considers these two subsequences to be "identical". He would like to find the longest such pair of subsequences so that the successive differences are identical. Your task is to help him do this.

-----Input:-----
The first line of the input will contain a single integer $N$ indicating the number of data points in each of Indraneel's student's data sets. This is followed by two lines, each containing $N$ integers.

-----Output:-----
The output consists of three lines. The first line of output contains a single integer indicating the length of the longest pair of subsequences (one from each sequence) that has identical successive differences. This is followed by two lines each containing the corresponding subsequences. If there is more than one answer, it suffices to print one.

-----Constraints:-----
- $1 \leq N \leq 150$.
- $0 \leq$ Each data point $\leq 1000$

-----Sample Input-----
7
3 8 4 23 9 11 28  
2 3 22 26 8 16 12 

-----Sample Output-----
4
3 4 23 9
2 3 22 8

def Point := Int × Int
def Rectangle := List Point

def calculate_rectangle_characteristics (points : Rectangle) : Float × Float × Float × Float × Float :=
  sorry

def length (points : Rectangle) : Float :=
  let (l, _, _, _, _) := calculate_rectangle_characteristics points
  l

def width (points : Rectangle) : Float :=
  let (_, w, _, _, _) := calculate_rectangle_characteristics points
  w

def area (points : Rectangle) : Float :=
  let (_, _, a, _, _) := calculate_rectangle_characteristics points
  a

def perimeter (points : Rectangle) : Float :=
  let (_, _, _, p, _) := calculate_rectangle_characteristics points
  p

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded