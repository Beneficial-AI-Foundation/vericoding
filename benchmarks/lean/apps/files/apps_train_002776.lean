/-
The purpose of this series is developing understanding of stastical problems in AS and A level maths. Let's get started with a simple concept in statistics: Mutually exclusive events.

The probability of an OR event is calculated by the following rule:

`P(A || B) = P(A) + P(B) - P(A && B)`

The probability of event A or event B happening is equal to the probability of event A plus the probability of event B minus the probability of event A and event B happening simultaneously.

Mutually exclusive events are events that cannot happen at the same time. For example, the head and tail results of a toin coss are mutually exclusive because they can't both happen at once. Thus, the above example for a coin toss would look like this:

`P(H || T) = P(H) + P(T) - P(H && T)`

Note that the probaility of tossing a coin and the result being both head and tails is 0.

`P(H || T) = (0.5) + (0.5) - (0)`
`P(H || T) = 1`

Thus the probability of a coin toss result being a heads or a tails is 1, in other words: certain.

Your task:

You are going to have to work out the probability of one roll of a die returning two given outcomes, or rolls. Given that dice rolls are mutually exclusive, you will have to implement the above forumala. To make this interesting (this is a coding challenge after all), these dice are not fair and thus the probabilites of receiving each roll is different.

You will be given a two-dimensional array containing the number each of the results (1-6) of the die and the probability of that roll for example `[1 , 0.23]` as well as the two rolls for example `1` and `5`. 

Given the two roll probabilities to calculate, return the probability of a single roll of the die returning either. If the total probability of the six rolls doesn't add up to one, there is a problem with the die; in this case, return null. 
Return your result as a string to two decimal places.

Example below:

`1 : 1/6`

`2 : 1/6`

`3 : 1/6`

`4 : 1/6`

`5 : 1/6`

`6 : 1/6`

If asked for the rolls `1` and `2` then you would need to sum the probabilities, both `1/6` therefore `2/6` and return this. As above, you will need to return it as a decimal and not a  fraction.
-/

-- <vc-helpers>
-- </vc-helpers>

def mutuallyExclusive (dice : List (Nat × Float)) (call1 : Nat) (call2 : Nat) : Option String := sorry

def sum_float_list (l : List Float) : Float := sorry

theorem invalid_probabilities_returns_none :
  ∀ (dice : List (Nat × Float)) (call1 call2 : Nat),
  sum_float_list (dice.map (fun p => p.2)) < 0.9 →
  mutuallyExclusive dice call1 call2 = none :=
sorry

theorem valid_probabilities_sum_correctly :
  mutuallyExclusive [(1, 0.2), (2, 0.2), (3, 0.2), (4, 0.2), (5, 0.2)] 1 2 = some "0.40" ∧
  mutuallyExclusive [(1, 0.3), (2, 0.3), (3, 0.4)] 1 2 = some "0.60" :=
sorry

/-
info: None
-/
-- #guard_msgs in
-- #eval mutually_exclusive *test1

/-
info: '0.30'
-/
-- #guard_msgs in
-- #eval mutually_exclusive *test2

/-
info: '0.20'
-/
-- #guard_msgs in
-- #eval mutually_exclusive *test3

-- Apps difficulty: introductory
-- Assurance level: unguarded