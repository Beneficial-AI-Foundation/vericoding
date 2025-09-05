Gennady is one of the best child dentists in Berland. Today n children got an appointment with him, they lined up in front of his office.

All children love to cry loudly at the reception at the dentist. We enumerate the children with integers from 1 to n in the order they go in the line. Every child is associated with the value of his cofidence p_{i}. The children take turns one after another to come into the office; each time the child that is the first in the line goes to the doctor.

While Gennady treats the teeth of the i-th child, the child is crying with the volume of v_{i}. At that the confidence of the first child in the line is reduced by the amount of v_{i}, the second one — by value v_{i} - 1, and so on. The children in the queue after the v_{i}-th child almost do not hear the crying, so their confidence remains unchanged.

If at any point in time the confidence of the j-th child is less than zero, he begins to cry with the volume of d_{j} and leaves the line, running towards the exit, without going to the doctor's office. At this the confidence of all the children after the j-th one in the line is reduced by the amount of d_{j}.

All these events occur immediately one after the other in some order. Some cries may lead to other cries, causing a chain reaction. Once in the hallway it is quiet, the child, who is first in the line, goes into the doctor's office.

Help Gennady the Dentist to determine the numbers of kids, whose teeth he will cure. Print their numbers in the chronological order.

-----Input-----

The first line of the input contains a positive integer n (1 ≤ n ≤ 4000) — the number of kids in the line. 

Next n lines contain three integers each v_{i}, d_{i}, p_{i} (1 ≤ v_{i}, d_{i}, p_{i} ≤ 10^6) — the volume of the cry in the doctor's office, the volume of the cry in the hall and the confidence of the i-th child.

-----Output-----

In the first line print number k — the number of children whose teeth Gennady will cure.

In the second line print k integers — the numbers of the children who will make it to the end of the line in the increasing order.

-----Examples-----
Input
5
4 2 2
4 1 2
5 2 4
3 3 5
5 1 2

Output
2
1 3 
Input
5
4 5 1
5 3 9
4 1 2
2 1 8
4 1 9

Output
4
1 2 4 5 

-----Note-----

In the first example, Gennady first treats the teeth of the first child who will cry with volume 4. The confidences of the remaining children will get equal to  - 2, 1, 3, 1, respectively. Thus, the second child also cries at the volume of 1 and run to the exit. The confidence of the remaining children will be equal to 0, 2, 0. Then the third child will go to the office, and cry with volume 5. The other children won't bear this, and with a loud cry they will run to the exit.

In the second sample, first the first child goes into the office, he will cry with volume 4. The confidence of the remaining children will be equal to 5,  - 1, 6, 8. Thus, the third child will cry with the volume of 1 and run to the exit. The confidence of the remaining children will be equal to 5, 5, 7. After that, the second child goes to the office and cry with the volume of 5. The confidences of the remaining children will be equal to 0, 3. Then the fourth child will go into the office and cry with the volume of 2. Because of this the confidence of the fifth child will be 1, and he will go into the office last.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: guarded