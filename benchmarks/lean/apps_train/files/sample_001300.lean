Chef Watson uses a social network called ChefBook, which has a new feed consisting of posts by his friends. Each post can be characterized by f - the identifier of the friend who created the post, p - the popularity of the post(which is pre-calculated by ChefBook platform using some machine learning algorithm) and s - the contents of the post which is a string of lower and uppercase English alphabets.
Also, Chef has some friends, which he has marked as special.
The algorithm used by ChefBook for determining the order of posts in news feed is as follows:

- Posts of special friends should be shown first, irrespective of popularity. Among all such posts the popular ones should be shown earlier.
- Among all other posts, popular posts should be shown earlier.

Given, a list of identifiers of Chef's special friends and a list of posts, you have to implement this algorithm for engineers of ChefBook and output the correct ordering of posts in the new feed. 

-----Input-----
First line contains N, number of special friends of Chef and M, the number of posts. Next line contains N integers A1, A2, ..., AN denoting the identifiers of special friends of Chef. Each of the next M lines contains a pair of integers and a string denoting f, p and s, identifier of the friend who created the post, the popularity of the post and the contents of the post, respectively. It is guaranteed that no two posts have same popularity, but the same friend might make multiple posts.

-----Output-----
Output correct ordering of posts in news feed in M lines. Output only the contents of a post.

-----Constraints-----
- 1 ≤ N, M ≤ 103
- 1 ≤ Ai, f, p ≤  105
- 1 ≤ length(s) ≤  100

-----Example-----
Input:
2 4
1 2
1 1 WhoDoesntLoveChefBook
2 2 WinterIsComing
3 10 TheseViolentDelightsHaveViolentEnds
4 3 ComeAtTheKingBestNotMiss

Output:
WinterIsComing
WhoDoesntLoveChefBook
TheseViolentDelightsHaveViolentEnds
ComeAtTheKingBestNotMiss

-----Explanation-----

First we should show posts created by friends with identifiers 1 and 2. Among the posts by these friends, the one with more popularity should be shown first.

Among remaining posts, we show those which are more popular first.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: interview
-- Assurance level: unguarded
