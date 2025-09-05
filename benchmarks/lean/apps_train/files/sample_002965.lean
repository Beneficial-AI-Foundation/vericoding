< PREVIOUS KATA
NEXT KATA >

## Task:

You have to write a function `pattern` which returns the following Pattern(See Examples) upto desired number of rows. 

* Note:`Returning` the pattern is not the same as `Printing` the pattern.

## Parameters:

    pattern(        n        ,        y        );
                    ^                 ^         
                    |                 |         
             Term upto which   Number of times  
              Basic Pattern     Basic Pattern   
                should be         should be     
                 created          repeated      
                                 vertically    

* Note: `Basic Pattern` means what we created in Complete The Pattern #12 i.e. a `simple X`.

## Rules/Note:

* The pattern should be created using only unit digits.
* If `n < 1` then it should return "" i.e. empty string.
* If `y <= 1` then the basic pattern should not be repeated vertically.
* `The length of each line is same`, and is equal to the length of longest line in the pattern.
* Range of Parameters (for the sake of CW Compiler) :
  + `n ∈ (-∞,50]`
  + `y ∈ (-∞,25]`
* If only one argument is passed then the function `pattern` should run as if `y <= 1`.
* The function `pattern` should work when extra arguments are passed, by ignoring the extra arguments.

## Examples:

#### Having Two Arguments:

##### pattern(4,3):

        1     1
         2   2 
          3 3  
           4   
          3 3  
         2   2 
        1     1
         2   2 
          3 3  
           4   
          3 3  
         2   2 
        1     1
         2   2 
          3 3  
           4   
          3 3  
         2   2 
        1     1

##### pattern(10,2):

        1                 1
         2               2 
          3             3  
           4           4   
            5         5    
             6       6     
              7     7      
               8   8       
                9 9        
                 0         
                9 9        
               8   8       
              7     7      
             6       6     
            5         5    
           4           4   
          3             3  
         2               2 
        1                 1
         2               2 
          3             3  
           4           4   
            5         5    
             6       6     
              7     7      
               8   8       
                9 9        
                 0         
                9 9        
               8   8       
              7     7      
             6       6     
            5         5    
           4           4   
          3             3  
         2               2 
        1                 1

#### Having Only One Argument:

##### pattern(25):

        1                                               1
         2                                             2 
          3                                           3  
           4                                         4   
            5                                       5    
             6                                     6     
              7                                   7      
               8                                 8       
                9                               9        
                 0                             0         
                  1                           1          
                   2                         2           
                    3                       3            
                     4                     4             
                      5                   5              
                       6                 6               
                        7               7                
                         8             8                 
                          9           9                  
                           0         0                   
                            1       1                    
                             2     2                     
                              3   3                      
                               4 4                       
                                5                        
                               4 4                       
                              3   3                      
                             2     2                     
                            1       1                    
                           0         0                   
                          9           9                  
                         8             8                 
                        7               7                
                       6                 6               
                      5                   5              
                     4                     4             
                    3                       3            
                   2                         2           
                  1                           1          
                 0                             0         
                9                               9        
               8                                 8       
              7                                   7      
             6                                     6     
            5                                       5    
           4                                         4   
          3                                           3  
         2                                             2 
        1                                               1

>>>LIST OF ALL MY KATAS<<<

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: unguarded
