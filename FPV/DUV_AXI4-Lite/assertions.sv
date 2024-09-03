module assertions (
    input logic clk,
    input logic reset,
    axi4_lite_if bfm
);

    // Ensure AWVALID is never asserted without AWADDR being valid
    property p1;
        @(posedge clk) disable iff (!reset) bfm.AWVALID |-> !$isunknown(bfm.AWADDR);
    endproperty
    assert property (p1);

    // Ensure ARVALID is never asserted without ARADDR being valid
    property p2;
        @(posedge clk) disable iff (!reset) bfm.ARVALID |-> !$isunknown(bfm.ARADDR);
    endproperty
    assert property (p2);

    // Ensure WVALID is never asserted without WDATA being valid
    property p3;
        @(posedge clk) disable iff (!reset) bfm.WVALID |-> !$isunknown(bfm.WDATA);
    endproperty
    assert property (p3);

    // Ensure RREADY is asserted only when RVALID is high
    property p4;
        @(posedge clk) disable iff (!reset) bfm.RREADY |-> bfm.RVALID;
    endproperty
    assert property (p4);

    // Ensure BREADY is asserted only when BVALID is high
    property p5;
        //@(posedge clk) disable iff (!reset) bfm.BREADY |-> bfm.BVALID;
	@(posedge clk) disable iff (reset) bfm.BREADY |-> bfm.BVALID;
    endproperty
    assert property (p5);

endmodule
