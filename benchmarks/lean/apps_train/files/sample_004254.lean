`Description:`

Given an input array (`arr`) of positive integers, the objective is to return an output array where each index represents the amount of times an element appeared (frequency) in the input array. 

More specifically, the element at each index of the output array will be an array (bucket) containing integers that appeared index-amount-of-times. 

Otherwise, slot nulls (JavaScript, Java), None's (Python) nils (Ruby), or NULL's (C/C++) where appropriate. A valid array will always be provided.

If an array of [1,2,3,4,4,5,5,5] is passed in, the expected output should be: [null, [1,2,3], [4], [5], null, null, null, null, null].

`Explanation:`

```python
# bucketize(arr) ======> outputArray
bucketize(1,2,3,4,4,5,5,5) ======> [None, [1, 2, 3], [4], [5], None, None, None, None, None]
```

An element cannot appear 0 times, so a null is placed at outputArray[0]. The elements 1, 2, and 3 appear once. This is why they are located at outputArray[1]. Notice the elements are grouped together in an array and sorted in ascending order. The element 4 appears twice. This is why it is located at outputArray[2]. The element 5 appears three times. This is why it is located at outputArray[3]. 

Although an integer could have possibly appeared four, five, six, seven, or eight times, this is not the case for this particular example. This is the reason why the elements at outputArray[4], outputArray[5], outputArray[6], outputArray[7], and outputArray[8] are all null values.

`Examples:`

```python
bucketize(2,2,4,4,6,6,9,9,9,9) ==> [None, None, [2,4,6], None, [9], None, None, None, None, None, None]
bucketize(3,3,3,3,2) ============> [None, [2], None, None, [3], None]
bucketize(5,5,5,5,5) ============> [None, None, None, None, None, [5]]
bucketize(77,3,40,40,40) ========> [None, [3,77], None, [40], None, None]
bucketize(16,7,5,3,6,23) ========> [None, [3,5,6,7,16,23], None, None, None, None, None]
```

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
