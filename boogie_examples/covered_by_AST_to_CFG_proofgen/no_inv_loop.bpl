procedure no_inv_loop() {
    var x : int;

    havoc x;
    while (x > 0)
    {
        x := x - 1;
    }
}