=====Function Descriptions=====
collections.Counter()
A counter is a container that stores elements as dictionary keys, and their counts are stored as dictionary values.

Sample Code
>>> from collections import Counter
>>> 
>>> myList = [1,1,2,3,4,5,3,2,3,4,2,1,2,3]
>>> print Counter(myList)
Counter({2: 4, 3: 4, 1: 3, 4: 2, 5: 1})
>>>
>>> print Counter(myList).items()
[(1, 3), (2, 4), (3, 4), (4, 2), (5, 1)]
>>> 
>>> print Counter(myList).keys()
[1, 2, 3, 4, 5]
>>> 
>>> print Counter(myList).values()
[3, 4, 4, 2, 1]

=====Problem Statement=====
Raghu is a shoe shop owner. His shop has X number of shoes.
He has a list containing the size of each shoe he has in his shop.
There are N number of customers who are willing to pay x_i amount of money only if they get the shoe of their desired size. Your task is to compute how much money Raghu earned.

=====Input Format=====
The first line contains X, the number of shoes.
The second line contains the space separated list of all the shoe sizes in the shop.
The third line contains N, the number of customers.
The next N lines contain the space separated values of the shoe size desired by the customer and x_i, the price of the shoe.

=====Constraints=====
0<X<10^3
0<N≤10^3
0<x_i<100
2<shoe size<20

=====Output Format=====
Print the amount of money earned by Raghu.

def calculate_shoe_shop_earnings (num_shoes : Nat) (shoe_sizes : List Nat) 
    (customer_requests : List (Nat × Nat)) : Nat :=
  sorry

def count_successful_sales (shoe_sizes : List Nat) (customer_requests : List (Nat × Nat)) : Nat :=
  sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded