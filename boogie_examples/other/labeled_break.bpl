procedure p() {
    var x : int;
    var y : int;
    var n : int;

    x := 0;
    y := 0;
    assume n > 0;

 ////////////////////////   
    
    outer_label:

    while (x > 0) 
    {
        /////////////
        while (y > 0)
        {
            //////////
            y := y+1;
            break outer_label;
            //////////
        }
        //////////////
        x := x+1;
        //////////////
    }

//////////////////////    

    return;
}