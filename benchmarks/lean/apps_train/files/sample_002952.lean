You have a set of four (4) balls labeled with different numbers: ball_1 (1), ball_2 (2), ball_3 (3) and ball(4) and we have 3 equal boxes for distribute them. The possible combinations of the balls, without having empty boxes, are:

```
 (1)            (2)        (3)(4)     
______        ______       _______ 

```

```
 (1)           (2)(4)        (3)
______         ______      ______

```

```
(1)(4)           (2)         (3)
______          ______      ______

```

```
  (1)           (2)(3)       (4)
_______         _______     ______

```

```
(1)(3)            (2)        (4)
_______         _______     ______
```

```
(1)(2)            (3)        (4)
_______         _______     ______
```
We have a total of **6** combinations.

Think how many combinations you will have with two boxes instead of three. You will obtain **7** combinations.

Obviously, the four balls in only box will give only one possible combination (the four balls in the unique box). Another particular case is the four balls in four boxes having again one possible combination(Each box having one ball).

What will be the reasonable result for a set of n elements with no boxes?

Think to create a function that may calculate the amount of these combinations of a set of ```n``` elements in ```k``` boxes.

You do no not have to check the inputs type that will be always valid integers.

The code should detect the cases when ```k > n```, returning "It cannot be possible!". 

Features of the random tests:
```
1 <= k <= n <= 800
```
Ruby version will be published soon.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
