///////////////////////////////////////////////////////////////////////////
// axi4_lite_Defs.sv - Global definitions for AXI4 Lite Bus
//
//
// Description:
// ------------
// Contains the global definitions such as parameters for the AXI4 Lite bus
///////////////////////////////////////////////////////////////////////////

package axi4_lite_Defs;

parameter

    Addr_Width = 32,                  // Address width of the bus

    Data_Width = 32;                  // Data width of the bus

typedef enum logic [1:0] {IDLE, ADDR, DATA, RESP} state;                                // four states for read and write operation
    
endpackage: axi4_lite_Defs
