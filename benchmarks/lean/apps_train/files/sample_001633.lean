Your task is the exact same as for the easy version. But this time, the marmots subtract the village's population P from their random number before responding to Heidi's request.

Also, there are now villages with as few as a single inhabitant, meaning that $1 \leq P \leq 1000$.

Can you help Heidi find out whether a village follows a Poisson or a uniform distribution?

-----Input-----

Same as for the easy and medium versions. But remember that now 1 ≤ P ≤ 1000 and that the marmots may provide positive as well as negative integers.

-----Output-----

Output one line per village, in the same order as provided in the input. The village's line shall state poisson if the village's distribution is of the Poisson type, and uniform if the answers came from a uniform distribution.

def identify_distribution (samples : List Int) : String :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded