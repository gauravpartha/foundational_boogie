procedure nested_loop2() {
    var x : int;
    var y : int;

    x := 10;
    y := 10;
    /////
    while (true)
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
                y := y - 1;
            }
            /////
            x := x - 1;
        }
    }
}