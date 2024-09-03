`include "axi4_lite_master.sv"
`include "axi4_lite_slave.sv"
`include "axi4_lite_if.sv"
`include "axi4_lite_Defs.sv"

import axi4_lite_Defs::*;

module axi4_lite_top(
input logic clk,                                           // system clock
input logic rstn,                                        // system reset, active low
input logic rd_en, wr_en,                                   // read and write enable
input logic [Addr_Width-1:0] Read_Address, Write_Address,   // read and write address variables
input logic [Data_Width-1:0] Write_Data                    // write data variable
);

//////////////////////////
//   BFM INSTANTIATION
//////////////////////////
axi4_lite_if bfm (.ACLK(clk), .ARESETN(rstn));

//Instantiate the DUV master and slave:
//Instantiate the master module
axi4_lite_master MP(
    .rd_en(rd_en),
    .wr_en(wr_en),
    .Read_Address(Read_Address),
    .Write_Address(Write_Address),
    .Write_Data(Write_Data),
    .M(bfm.master_if)
);


// instantiate the slave module
axi4_lite_slave SP(
    .S(bfm.slave_if)
);


`ifdef FORMAL

    // 1) Ensure AWVALID is never asserted without AWADDR being valid
    property valid;
        //@(posedge clk) disable iff (!rstn) (!bfm.AWVALID |-> !(bfm.AWVALID && bfm.AWADDR));///also ok
@(posedge clk) disable iff (!rstn) (bfm.AWVALID |-> !$isunknown(bfm.AWADDR));
    endproperty
    assert property (valid);

    // 2) Ensure ARVALID is never asserted without ARADDR being valid
    property ARVALID_no_assertion_without_ARADDR;
      @(posedge clk) disable iff (!rstn) (
         !bfm.ARVALID |-> !$isunknown(bfm.ARADDR)
      ); 
    endproperty
    assert property (ARVALID_no_assertion_without_ARADDR) else $error("ARVALID asserted without valid ARADDR");

    //3) Ensure WVALID is never asserted without WDATA being valid (is unknown use when need to ensure signal is completely free without proceeding with logic or assertion)
   property valid_wdata_never_without_valid_wdata;
	@(posedge clk) disable iff (!rstn) bfm.WVALID |-> bfm.WVALID && !$isunknown(bfm.WDATA);
   endproperty
  assert property (valid_wdata_never_without_valid_wdata);
   
  //4) Ensure RREADY is asserted only when RVALID is high
   property ensure_RREADY_assertion_only_when_RVALID_is_high;
       @(posedge clk) disable iff (!rstn) ($isunknown(bfm.RREADY) |-> $isunknown(bfm.RVALID)); endproperty
   assert property (ensure_RREADY_assertion_only_when_RVALID_is_high) else $error("RREADY is asserted when RVALID is low!");



  //5) When AWVALID and AWREADY are high at the same time, the next cycle AWVALID goes low
    property valid_low_next_cycle;
       @(posedge clk) disable iff (!rstn) // Global clock and reset
          bfm.AWVALID && bfm.AWREADY && $rose(clk) |-> ##1 !bfm.AWVALID;
    endproperty
    assert property (valid_low_next_cycle);
  

    //6. Counter example
    //property ensure_valid_ready;
      //logic BVALID;
      //logic BREADY;
      //@(posedge clk) disable iff (!rstn)
        //  (bfm.BREADY |-> ##1 bfm.BVALID);
   //endproperty

//assert property (ensure_valid_ready) else $error("BREADY is asserted when BVALID is not high");


//7. Ensure RREADY is asserted only when BVALID is high
//property ensure_RREADY_asserted_only_when_BVALID_is_high;
  //  @(posedge clk) disable iff (!rstn)
   // (bfm.AWVALID && !bfm.AWREADY) |-> !bfm.WREADY;
//endproperty

//assert property (ensure_RREADY_asserted_only_when_BVALID_is_high) else $error("Violation: RREADY is asserted when BVALID is low");



`endif // FORMAL

endmodule