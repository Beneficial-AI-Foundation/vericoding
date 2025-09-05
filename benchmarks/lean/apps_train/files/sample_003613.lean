# Task
 In a black and white image we can use `1` instead of black pixels and `0` instead of white pixels. 

 For compression image file we can reserve pixels by consecutive pixels who have the same color. 

 Your task is to determine how much of black and white pixels is in each row sorted by place of those.

# Example:

 For `height=2,width=100 and compressed=[40,120,40,0]`

 The result should be `[[40,60],[0,60,40,0]]`

 Sum of compressed array always divisible by width and height of image.

 Pixels available is in Compressed array in this order:

 `[Black,White,Black,White,Black,White,...]`

 ![](http://s3.picofile.com/file/8194350650/Compressed_Image_1_.png)

 For `height=2,width=100 and compressed=[0, 180, 20, 0]`

 The result should be `[[0,100],[0,80,20,0]]`

 ![](http://s6.picofile.com/file/8194348868/Compressed_Image.png)

# Input/Output

- `[input]` integer `height`

  Height of image

- `[input]` integer `width`

  Width of image

- `[input]` integer array `compressed`

  Consecutive pixels

- `[output]` 2D integer array

 The black and white pixels in each row.

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded