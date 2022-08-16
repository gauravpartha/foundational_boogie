procedure nested_loop3() {
    var x : int;
    var y : int;
    var z : int;

    x := 10;
    y := 10;
    z := 10;
    /////
    while (z > 0)
    {
        /////
        while (x > 0)
            invariant x >= 0;
        {
            /////////
            while (y > 0)
                invariant y >= 0;
            {
                //////
                z := z - 1;
                y := y - 1;
            }
            /////
            x := x - 1;
        }
    }
}