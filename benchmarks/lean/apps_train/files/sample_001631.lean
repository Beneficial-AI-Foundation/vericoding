Good job! Now that Heidi is able to distinguish between Poisson and uniform distributions, she is in a good position to actually estimate the populations.

Can you help Heidi estimate each village's population?

-----Input-----

Same as the easy version.

-----Output-----

Output one line per village, in the same order as provided in the input, containing your (integer) population estimate.

Your answer is considered correct if it is an integer that falls into the interval $[ \lfloor 0.95 \cdot P \rfloor, \lceil 1.05 \cdot P \rceil ]$, where P is the real population of the village, used to create the distribution (either Poisson or uniform) from which the marmots drew their answers.

def minimum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | (x::xs) => xs.foldl min x

def maximum (l : List Nat) : Nat :=
  match l with
  | [] => 0
  | (x::xs) => xs.foldl max x

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
