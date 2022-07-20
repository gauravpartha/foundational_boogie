procedure nested_loop() {
    var x : int;
    var y : int;

    ///// bigblock_0 , bigblock_1
    ///// cont_0 = KSeq bigblock_6 cont_6
    ///// cont_1 = KEndBlock (KSeq bigblock_6 cont_6)
    x := 10;
    y := 10;
    while (x > 0)
        invariant x >= 0;
    {


        ///////// bigblock_2, bigblock_3
        ///////// cont_2 = KSeq bigblock_5 cont_5
        ///////// cont_3 = KEndBlock (KSeq bigblock_5 cont_5)
        while (y > 0)
            invariant y >= 0;
        {
            ////// bigblock_4
            ////// cont_4 = KSeq bigblock_3 cont_3 
            y := y - 1;

        }
        ///// bigblock_5
        ///// --> cont_5 = KSeq bigblock_1 cont_1
        x := x - 1; 


    }

    //bigblock_6
    //empty final big block --> cont_6 = KStop
    
}