# Definition

**_Balanced number_** is the number that * **_The sum of_** all digits to the **_left of the middle_** digit(s) and the sum of all digits to the **_right of the middle_** digit(s) are **_equal_***.

____

# Task

**_Given_** a number, **_Find if it is Balanced or not_** . 
____

# Warm-up (Highly recommended)

# [Playing With Numbers Series](https://www.codewars.com/collections/playing-with-numbers)
___

# Notes 

* *If* the **_number has an odd number of digits_**  then **_there is only one middle digit_**,  e.g.  `92645`  has middle digit `6`;  **_otherwise_**, there are **_two middle digits_** , e.g.  `1301`  has middle digits  `3`  and  `0` 

* **_The middle digit(s)_**  should  **_not_** be considered when *determining whether a number is balanced or not*, **_e.g_**  `413023`  is a **_balanced number because the left sum and right sum are both_**   `5`.

* **_Number_** *passed is always*  **_Positive_** .

* **_Return_** *the result as* **_String_**

___

# Input >> Output Examples

```
(balanced-num 7) ==> return "Balanced"
```

## **_Explanation_**:

* **_Since_** , **_The sum of_** *all digits to the* **_left of the middle_** digit (0) 

* and **_the sum of_** *all digits to the* **_right of the middle_** digit (0) are **_equal_**  , **_then_** *It's* **_Balanced_**
___

```
(balanced-num 295591) ==> return "Not Balanced"
```

## **_Explanation_**:

* **_Since_** , **_The sum of_** *all digits to the* **_left of the middle_** digits (11) 

* and **_the sum of_** *all digits to the* **_right of the middle_** digits (10) are **_Not equal_**  , **_then_** *It's* **_Not Balanced_** 

* **_Note_** : **_The middle digit(s)_**  *are* **_55_** . 

___
```
(balanced-num 959) ==> return "Balanced"
```

## **_Explanation_**:

* **_Since_** , **_The sum of_** *all digits to the* **_left of the middle_** digits (9) 

* and **_the sum of_** *all digits to the* **_right of the middle_** digits (9) are **_equal_**  , **_then_** *It's* **_Balanced_** 

* **_Note_** : **_The middle digit_**  *is* **_5_** . 
____

```
(balanced-num 27102983) ==> return "Not Balanced"
```

## **_Explanation_**:

* **_Since_** , **_The sum of_** *all digits to the* **_left of the middle_** digits (10) 

* and **_the sum of_** *all digits to the* **_right of the middle_** digits (20) are **_Not equal_**  , **_then_** *It's* **_Not Balanced_** 

* **_Note_** : **_The middle digit(s)_**  *are* **_02_** . 

___
___
___

# [Playing with Numbers Series](https://www.codewars.com/collections/playing-with-numbers)

# [Playing With Lists/Arrays Series](https://www.codewars.com/collections/playing-with-lists-slash-arrays)

# [For More Enjoyable Katas](http://www.codewars.com/users/MrZizoScream/authored)
___

## ALL translations are welcomed

## Enjoy Learning !!
# Zizou

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded