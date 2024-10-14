**Snippet of Two Specification: Proposed Approach-Hallucination Reduction**


At Zero Shot Prompting 

Spec	Descriptions	GPT 3.5	GPT 4	RAG-LLM (Our)	Evaluation Criteria
Spec 1	Ensure AWVALID is never asserted without AWADDR being valid	property p_awvalid_awaddr_valid;
    @(posedge clk)
    disable iff (rst_n === 0)
    (AWVALID == 1'b1) |-> (AWADDR == 1'b1);
endproperty
assert property (p_awvalid_awaddr_valid);	property AWVALID_without_AWADDR_valid;
  @(posedge clk) disable iff (reset) (AWVALID && !AWADDR_valid) |-> 0;
endproperty

assert property (AWVALID_without_AWADDR_valid)
  else $error("Assertion failed: AWVALID is asserted without AWADDR being valid");	property valid;
@(posedge clk) disable iff (!rstn) (AWVALID |-> !$isunknown(AWADDR));
    endproperty
    assert property (valid);	Visual Inspection 
		Assumptions + Failed	Misleading CEs	Verified 	BMC
Spec 2	Ensure ARVALID is never asserted without ARADDR being valid	property p_arvalid_araddr_valid;
    @(posedge clk)
    disable iff (rst_n === 0)
    (ARVALID == 1'b1) |-> (ARADDR == 1'b1);
endproperty

assert property (p_arvalid_araddr_valid);	property ARVALID_asserted_with_ARADDR_valid;
  @(posedge clk) disable iff (reset) ARVALID |-> ARADDR_valid;
endproperty

assert property (ARVALID_asserted_with_ARADDR_valid)
  else $error("Assertion failed: ARVALID is asserted without ARADDR being valid"); 	Property ARVALID_no_assertion_without_ARADDR;
  @(posedge clk) disable iff (!rstn) 
(!ARVALID |-> !$isunknown(ARADDR)); 
    endproperty
    assert property (ARVALID_no_assertion_without_ARADDR)
	Visual Inspection 
		Assumptions (Hallucination) + Failed	Misleading CEs	Verified 	BMC


**Summary of Results (RAG-LLM): Designer Tailored Specification Conforming to HLS and FPV Evaluation**

No.	Spec
(Tailored by Designer)	HLS-Conformance	SVA 	FPV (BMC)
1	Ensure AWVALID is never asserted without AWADDR being valid
	- The provided context describes the signals AWVALID and AWADDR which are used in the AXI write address channel. The context also explains that these signals work together to ensure proper write address information is transmitted. This aligns with the requirement in the specification sentence to ensure AWVALID is never asserted without AWADDR being valid.	property valid;
@(posedge clk) disable iff (!rstn) (bfm.AWVALID |-> !$isunknown(bfm.AWADDR));
    endproperty
    assert property (valid);

	Verified 
2	Ensure ARVALID is never asserted without ARADDR being valid	- Conforming: The specification context mentions the signals related to address channels which include `ARADDR` and `ARVALID`, supporting the requirement of ensuring that `ARVALID` is never asserted without `ARADDR` being valid.	 Property ARVALID_no_assertion_without_ARADDR;
  @(posedge clk) disable iff (!rstn) 
(!bfm.ARVALID |-> !$isunknown(bfm.ARADDR)); 
    endproperty
    assert property (ARVALID_no_assertion_without_ARADDR)
else $error("ARVALID asserted without valid ARADDR");

  
  	Verified 
3	Ensure WVALID is never asserted without WDATA being valid	- Signal WVALID fulfills the condition specified in the assertion as it is never asserted without WDATA being valid.	Property valid_wdata_never_without_valid_wdata;
	@(posedge clk) disable iff (!rstn) bfm.WVALID |-> bfm.WVALID && !$isunknown(bfm.WDATA);
   endproperty
  assert property (valid_wdata_never_without_valid_wdata);
   	Verified 
4	Ensure RREADY is asserted only when RVALID is high	The given SystemVerilog assertion is consistent with the specification since it ensures RREADY is only asserted when RVALID is high by using the global clock signal 'clk' and global reset signal 'rstn'.	 property ensure_RREADY_assertion_only_when_RVALID_is_high;
       @(posedge clk) disable iff (!rstn) ($isunknown(bfm.RREADY) |-> $isunknown(bfm.RVALID)); endproperty
   assert property (ensure_RREADY_assertion_only_when_RVALID_is_high) else $error("RREADY is asserted when RVALID is low!");	Verified
5	When AWVALID and AWREADY are high at the same time, the next cycle AWVALID goes low	Conforming: In both Spec 1 and Spec 2, AWVALID is defined as Master Write address valid and AWREADY is defined as Slave Write address ready, which confirms to the requirement in the spec.	property valid_low_next_cycle;
       @(posedge clk) disable iff (!rstn) // Global clock and reset
          bfm.AWVALID && bfm.AWREADY && $rose(clk) |-> ##1 !bfm.AWVALID;
    endproperty
    assert property (valid_low_next_cycle);
	Verified 
6	Ensure BREADY is asserted only when BVALID is high	This context does not provide specific information related to BREADY and BVALID signals.	property ensure_valid_ready;
      logic BVALID;
      logic BREADY;
      @(posedge clk) disable iff (!rstn)
       (bfm.BREADY |-> ##1 bfm.BVALID);
   endproperty

assert property (ensure_valid_ready) else $error("BREADY is asserted when BVALID is not high");	Counter-Example 
7	Ensure RREADY is asserted only when BVALID is high	The provided specification context does not contain direct information related to RREADY and BVALID signals to confirm conformity with the generated SVA.	property ensure_RREADY_asserted_only_when_BVALID_is_high;
 @(posedge clk) disable iff (!rstn)
 (bfm.AWVALID && !bfm.AWREADY) |-> !bfm.WREADY; endproperty

assert property (ensure_RREADY_asserted_only_when_BVALID_is_high) else $error("Violation: RREADY is asserted when BVALID is low");	Counter-Example

