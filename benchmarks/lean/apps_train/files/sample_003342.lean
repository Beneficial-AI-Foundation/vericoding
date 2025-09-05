# Introduction and Warm-up (Highly recommended)

# [Playing With Lists/Arrays Series](https://www.codewars.com/collections/playing-with-lists-slash-arrays)
___

# Task

**_Given_** an *array/list [] of integers* , **_Find_** **_The maximum difference_** *between the successive elements in its sorted form*. 
___

# Notes 

* **_Array/list_** size is *at least 3*  .

* **_Array/list's numbers_**  Will be **mixture of positives and negatives also zeros_**  

* **_Repetition_** of numbers in *the array/list could occur*.

* **_The Maximum Gap_** is *computed Regardless the sign*.

___

# Input >> Output Examples 

```
maxGap ({13,10,5,2,9}) ==> return (4)
```

## **_Explanation_**: 

* **_The Maximum Gap_** *after sorting the array is* `4` , *The difference between*   ``` 9 - 5 = 4 ``` .
___

```
maxGap ({-3,-27,-4,-2}) ==> return (23)
```
## **_Explanation_**: 

* **_The Maximum Gap_** *after sorting the array is* `23` , *The difference between*   ` |-4- (-27) | = 23` .

*  **_Note_** : *Regardless the sign of negativity* .
___

```
maxGap ({-7,-42,-809,-14,-12}) ==> return (767)  
```
## **_Explanation_**: 

* **_The Maximum Gap_** *after sorting the array is* `767` , *The difference between*   ` | -809- (-42) | = 767` .

*  **_Note_** : *Regardless the sign of negativity* .
___

```
maxGap ({-54,37,0,64,640,0,-15}) //return (576)
```
## **_Explanation_**: 

* **_The Maximum Gap_** *after sorting the array is* `576` , *The difference between*   ` | 64 - 640 | = 576` .

*  **_Note_** : *Regardless the sign of negativity* .
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

def maximum (xs : List Int) : Int := sorry
def minimum (xs : List Int) : Int := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
