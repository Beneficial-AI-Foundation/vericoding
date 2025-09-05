Chef is a really nice and respectful person, in sharp contrast to his little brother, who is a very nasty and disrespectful person. Chef always sends messages to his friends in all small letters, whereas the little brother sends messages in all capital letters.
You just received a message given by a string s. You don't know whether this message is sent by Chef or his brother. Also, the communication channel through which you received the message is erroneous and hence can flip a letter from uppercase to lowercase or vice versa. However, you know that this channel can make at most K such flips.
Determine whether the message could have been sent only by Chef, only by the little brother, by both or by none.

-----Input-----

- The first line of the input contains a single integer T denoting the number of test cases. The description of T test cases follows.
- The first line of each test case contains two space-separated integers N and K denoting the length of the string s and the maximum number of flips that the erroneous channel can make.
- The second line contains a single string s denoting the message you received.

-----Output-----
For each test case, output a single line containing one string — "chef", "brother", "both" or "none".

-----Constraints-----
- 1 ≤ T ≤ 1000
- 1 ≤ N ≤ 100
- 0 ≤ K ≤ N
- s consists only of (lowercase and uppercase) English letters

-----Example-----
Input

4
5 1
frauD
5 1
FRAUD
4 4
Life
10 4
sTRAWBerry

Output

chef
brother
both
none

-----Explanation-----
Example case 1: Only one flip is possible. So it is possible that Chef sent "fraud" and the channel flipped the last character to get "frauD". However, it is not possible for the brother to have sent "FRAUD", because then it would need 4 flips. Hence the answer is "chef".
Example case 2: Only one flip is possible. So it is possible that the brother sent "FRAUD" and the channel didn't flip anything. However, it is not possible for Chef to have sent "fraud", because then it would need 5 flips. Hence the answer is "brother".
Example case 3: Four flips are allowed. It is possible that Chef sent "life" and the channel flipped the first character to get "Life". It is also possible that the brother sent "LIFE" and the channel flipped the last three characters to get "Life". Hence the answer is "both".
Example case 4: Four flips are allowed. It is not possible that Chef sent "strawberry", because it would need five flips to get "sTRAWBerry". It is also not possible that the brother sent "STRAWBERRY", because that would also need five flips. Hence the answer is "none".

def isUpper (c : Char) : Bool := sorry
def isLower (c : Char) : Bool := sorry

def countUpper (s : String) : Nat := sorry
def countLower (s : String) : Nat := sorry

inductive MessageType where
  | chef
  | brother  
  | both
  | none
  deriving Repr

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded