There are n cabs in a city numbered from 1 to n. The city has a rule that only one cab can run in the city at a time. Cab picks up the customer and drops him to his destination. Then the cab gets ready to pick next customer. There are m customers in search of cab. First customer will get the taxi first. You have to find the nearest cab for each customer. If two cabs have same distance then the cab with lower number is preferred.

Your task is to find out minimum distant cab for each customer.

Input:

The first line of the input contains an integer T denoting the number of test cases.
The description of T test cases follows.
The first line of each test case contains two space-separated integers N and M, denoting the number of cabs and the number of customers.

The next N lines contain two space-separated integers x[i] and y[i], denoting the initial position of the ith cab.

Next line contains an integer M denoting number of customers.
The next M lines contain four space seperated integers sx[i], sy[i], dx[i], dy[i], denoting the current location and the destination of the ith customer.

Output:

Output the nearest cab number for each customer.

Constraints:

1<=t<=10

1<=n,m<=1000

-10^9<=x[i] , y[i] , sx[i] , sy[i] , dx[i] , dy[i]<=10^9

Example:
Input:

1

3 2

1 3

3 2

3 5

2 3 3 4

5 3 4 1

Output:

1

1

Explanation:

The distance of cab1 from customer1 = sqrt((1-2)^2 + (3-3)^2) = 1

The distance of cab2 from customer1 = sqrt(2)

The distance of cab3 from customer1 = sqrt(5)

So output for customer1 is 1

Now location of cab1 is (3,4)

The distance of cab1 from customer2 = sqrt((3-5)^2 + (4-3)^2) = sqrt(5)

The distance of cab2 from customer2 = sqrt(5)

The distance of cab3 from customer2 = sqrt(8)

So output for customer2 is 1

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: guarded
