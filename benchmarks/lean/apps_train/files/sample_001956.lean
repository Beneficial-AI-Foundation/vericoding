Vasya's telephone contains n photos. Photo number 1 is currently opened on the phone. It is allowed to move left and right to the adjacent photo by swiping finger over the screen. If you swipe left from the first photo, you reach photo n. Similarly, by swiping right from the last photo you reach photo 1. It takes a seconds to swipe from photo to adjacent.

For each photo it is known which orientation is intended for it — horizontal or vertical. Phone is in the vertical orientation and can't be rotated. It takes b second to change orientation of the photo.

Vasya has T seconds to watch photos. He want to watch as many photos as possible. If Vasya opens the photo for the first time, he spends 1 second to notice all details in it. If photo is in the wrong orientation, he spends b seconds on rotating it before watching it. If Vasya has already opened the photo, he just skips it (so he doesn't spend any time for watching it or for changing its orientation). It is not allowed to skip unseen photos.

Help Vasya find the maximum number of photos he is able to watch during T seconds.

-----Input-----

The first line of the input contains 4 integers n, a, b, T (1 ≤ n ≤ 5·10^5, 1 ≤ a, b ≤ 1000, 1 ≤ T ≤ 10^9) — the number of photos, time to move from a photo to adjacent, time to change orientation of a photo and time Vasya can spend for watching photo.

Second line of the input contains a string of length n containing symbols 'w' and 'h'. 

If the i-th position of a string contains 'w', then the photo i should be seen in the horizontal orientation.

If the i-th position of a string contains 'h', then the photo i should be seen in vertical orientation.

-----Output-----

Output the only integer, the maximum number of photos Vasya is able to watch during those T seconds.

-----Examples-----
Input
4 2 3 10
wwhw

Output
2

Input
5 2 4 13
hhwhh

Output
4

Input
5 2 4 1000
hhwhh

Output
5

Input
3 1 100 10
whw

Output
0

-----Note-----

In the first sample test you can rotate the first photo (3 seconds), watch the first photo (1 seconds), move left (2 second), rotate fourth photo (3 seconds), watch fourth photo (1 second). The whole process takes exactly 10 seconds.

Note that in the last sample test the time is not enough even to watch the first photo, also you can't skip it.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: competition
-- Assurance level: unguarded