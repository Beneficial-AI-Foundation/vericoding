Create a function `sierpinski` to generate an ASCII representation of a Sierpinski triangle of order **N**. 

Seperate each line with `\n`. You don't have to check the input value.

The output should look like this: 

     sierpinski(4)
                   *               
                  * *              
                 *   *             
                * * * *            
               *       *           
              * *     * *          
             *   *   *   *         
            * * * * * * * *        
           *               *       
          * *             * *      
         *   *           *   *     
        * * * *         * * * *    
       *       *       *       *   
      * *     * *     * *     * *  
     *   *   *   *   *   *   *   * 
    * * * * * * * * * * * * * * * *

def String.lines (s : String) : List String := sorry

def String.count (s : String) (c : Char) : Nat := sorry

-- <vc-helpers>
-- </vc-helpers>

-- Apps difficulty: introductory
-- Assurance level: guarded_and_plausible