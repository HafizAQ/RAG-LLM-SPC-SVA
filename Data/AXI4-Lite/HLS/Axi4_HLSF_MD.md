# AMBA


® ™ ™
# AXI and ACE Protocol
 Specification

**™** **™** **™**

### AXI3, AXI4, and AXI4-Lite

**™**

### ACE and ACE-Lite


-----

# Part A

### AMBA AXI3 and AXI4 Protocol Specification


-----

-----

## Chapter A1 Introduction

This chapter introduces the architecture of the AXI protocol and the terminology used in this specification. It
contains the following sections:

-  _About the AXI protocol_ on page A1-22

-  _AXI revisions_ on page A1-23

-  _AXI Architecture_ on page A1-24

-  _Terminology_ on page A1-27 .


-----

**A1.1** **About the AXI protocol**

The AMBA AXI protocol supports high-performance, high-frequency system designs.

The AXI protocol:

-  is suitable for high-bandwidth and low-latency designs

-  provides high-frequency operation without using complex bridges

-  meets the interface requirements of a wide range of components

-  is suitable for memory controllers with high initial access latency

-  provides flexibility in the implementation of interconnect architectures

-  is backward-compatible with existing AHB and APB interfaces.

The key features of the AXI protocol are:

-  separate address/control and data phases

-  support for unaligned data transfers, using byte strobes

-  uses burst-based transactions with only the start address issued

-  separate read and write data channels, that can provide low-cost _Direct Memory Access_ (DMA)

-  support for issuing multiple outstanding addresses

-  support for out-of-order transaction completion

-  permits easy addition of register stages to provide timing closure.

The AXI protocol includes the optional extensions that cover signaling for low-power operation.

The AXI protocol includes the AXI4-Lite specification, a subset of AXI4 for communication with simpler control
register style interfaces within components. See Chapter B1 _AMBA AXI4-Lite_ .


-----

**A1.2** **AXI revisions**

Earlier issues of this document describe earlier versions of the AMBA AXI Protocol Specification. In particular,
Issue B of the document describes the version that is now called AXI3.

Issue C adds the definition of an extended version of the protocol called AXI4 and a new interface, AXI4-Lite, that
provides a simpler control register interface, for applications that do not require the full functionality of AXI4.

Issue D integrates the definitions of AXI3 and AXI4 which were presented separately in Issue C.

Issue E adds clarifications, recommendations, and specifies new capabilities. To maintain compatibility, a property
is used to declare a new capability. If a property is not declared, it is considered False.

Table A1-1 summarizes the new properties and the default value that applies for a component that does not have a
declared value.

**Table A1-1 Properties that specify system capability**

**Property** **Description** **Default**


Ordered_Write_Observation Improved support for the _Producer/Consumer_ ordering model. See _Ordered write_
_observation_ on page A6-91


False


Multi_Copy_Atomicity Support for multi-copy atomicity. See _Multi-copy write atomicity_ on page A7-95 False

**Note**

Some previous issues of this document included a version number in the title. That version number does not refer
to the version of the AXI protocol.


-----

**A1.3** **AXI Architecture**

The AXI protocol is burst-based and defines the following independent transaction channels:

-  read address

-  read data

-  write address

-  write data

-  write response.

An address channel carries control information that describes the nature of the data to be transferred. The data is
transferred between master and slave using either:

-  A write data channel to transfer data from the master to the slave. In a write transaction, the slave uses the
write response channel to signal the completion of the transfer to the master.

-  A read data channel to transfer data from the slave to the master.

The AXI protocol:

-  permits address information to be issued ahead of the actual data transfer

-  supports multiple outstanding transactions

-  supports out-of-order completion of transactions.

Figure A1-1 shows how a read transaction uses the read address and read data channels.








|Master interface|Read address channel|Col3|Col4|Col5|Col6|Col7|Slave interface|
|---|---|---|---|---|---|---|---|
||Address and control|||||||
||Read data channel|||||||
|||Read data|Read data|Read data|Read data|||
|||||||||


**Figure A1-1 Channel architecture of reads**

Figure A1-2 shows how a write transaction uses the write address, write data, and write response channels.








|Master interface|Write address channel|Col3|Col4|Col5|Col6|Col7|Slave interface|
|---|---|---|---|---|---|---|---|
||Address and control|||||||
||Write data channel|||||||
|||Write data|Write data|Write data|Write data|||
||Write response channel|||||||
|||||||Write response||
|||||||||


**Figure A1-2 Channel architecture of writes**


-----

**A1.3.1** **Channel definition**

Each of the independent channels consists of a set of information signals and **VALID** and **READY** signals that
provide a two-way handshake mechanism. See _Basic read and write transactions_ on page A3-39 .

The information source uses the **VALID** signal to show when valid address, data or control information is available
on the channel. The destination uses the **READY** signal to show when it can accept the information. Both the read
data channel and the write data channel also include a **LAST** signal to indicate the transfer of the final data item in
a transaction.

**Read and write address channels**

Read and write transactions each have their own address channel. The appropriate address channel carries all of the
required address and control information for a transaction.

**Read data channel**

The read data channel carries both the read data and the read response information from the slave to the master, and
includes:

-  the data bus, that can be 8, 16, 32, 64, 128, 256, 512, or 1024 bits wide

-  a read response signal indicating the completion status of the read transaction.

**Write data channel**

The write data channel carries the write data from the master to the slave and includes:

-  the data bus, that can be 8, 16, 32, 64, 128, 256, 512, or 1024 bits wide

-  a byte lane strobe signal for every eight data bits, indicating which bytes of the data are valid.

Write data channel information is always treated as buffered, so that the master can perform write transactions
without slave acknowledgement of previous write transactions.

**Write response channel**

A slave uses the write response channel to respond to write transactions. All write transactions require completion
signaling on the write response channel.

As Figure A1-2 on page A1-24 shows, completion is signaled only for a complete transaction, not for each data
transfer in a transaction.

**A1.3.2** **Interface and interconnect**

A typical system consists of a number of master and slave devices connected together through some form of
interconnect, as Figure A1-3 shows.





**Figure A1-3 Interface and interconnect**

The AXI protocol provides a single interface definition, for the interfaces:

-  between a master and the interconnect

-  between a slave and the interconnect

-  between a master and a slave.

This interface definition supports a variety of different interconnect implementations.


-----

**Note**

An interconnect between devices is equivalent to another device with symmetrical master and slave ports to which
real master and slave devices can be connected.

**Typical system topologies**

Most systems use one of three interconnect topologies:

-  shared address and data buses

-  shared address buses and multiple data buses

-  multilayer, with multiple address and data buses.

In most systems, the address channel bandwidth requirement is significantly less than the data channel bandwidth
requirement. Such systems can achieve a good balance between system performance and interconnect complexity
by using a shared address bus with multiple data buses to enable parallel data transfers.

**A1.3.3** **Register slices**

Each AXI channel transfers information in only one direction, and the architecture does not require any fixed
relationship between the channels. This means a register slice can be inserted at almost any point in any channel, at
the cost of an additional cycle of latency.

**Note**

This makes possible:

-  a trade-off between cycles of latency and maximum frequency of operation

-  a direct, fast connection between a processor and high performance memory, but to use simple register slices
to isolate a longer path to less performance critical peripherals.


-----

**A1.4** **Terminology**

This section summarizes terms that are used in this specification, and are defined in the _Glossary_, or elsewhere.
Where appropriate, terms listed in this section link to the corresponding glossary definition.

**A1.4.1** **AXI components and topology**

The following terms describe AXI components:

-  _Component_ .

-  _Master component_ .

-  _Slave component_ . Slave components include _Memory slave component_ s and _Peripheral slave component_ s.

-  _Interconnect component_ .

For a particular AXI transaction, _Upstream_ and _Downstream_ refer to the relative positions of AXI components
within the AXI topology.

**A1.4.2** **AXI transactions, and memory types**

When an AXI master initiates an AXI operation, targeting an AXI slave:

-  the complete set of required operations on the AXI bus form the AXI _Transaction_

-  any required payload data is transferred as an AXI _Burst_

-  a burst can comprise multiple data transfers, or AXI _Beat_ s.

**A1.4.3** **Caches and cache operation**

This specification does not define standard cache terminology, that is defined in any reference work on caching.
However, the glossary entries for _Cache_ and _Cache line_ clarify how these terms are used in this document.

**A1.4.4** **Temporal description**

The AXI specification uses the term _In a timely manner_ .


-----

-----

## Chapter A2 Signal Descriptions

This chapter introduces the AXI interface signals. Most of the signals are required for both AXI3 and AXI4
implementations of the protocol, and the tables summarizing the signals identify the exceptions. This chapter
contains the following sections:

-  _Global signals_ on page A2-30

-  _Write address channel signals_ on page A2-31

-  _Write data channel signals_ on page A2-32

-  _Write response channel signals_ on page A2-33

-  _Read address channel signals_ on page A2-34

-  _Read data channel signals_ on page A2-35

-  _Low-power interface signals_ on page A2-36 .

Later chapters define the signal parameters and usage.


-----

**A2.1** **Global signals**

Table A2-1 shows the global AXI signals. These signals are used by the AXI3 and AXI4 protocols.

**Table A2-1 Global signals**

**Signal** **Source** **Description**

**ACLK** Clock source Global clock signal. See _Clock_ on page A3-38 .

**ARESETn** Reset source Global reset signal, active LOW. See _Reset_ on page A3-38 .

All signals are sampled on the rising edge of the global clock.


-----

**A2.2** **Write address channel signals**

Table A2-2 shows the AXI write address channel signals. Unless the description indicates otherwise, a signal is used
by AXI3 and AXI4.

**Table A2-2 Write address channel signals**

**Signal** **Source** **Description**

**AWID** Master Write address ID. This signal is the identification tag for the write address group
of signals. See _Transaction ID_ on page A5-79 .

**AWADDR** Master Write address. The write address gives the address of the first transfer in a write
burst transaction. See _Address structure_ on page A3-46 .

**AWLEN** Master Burst length. The burst length gives the exact number of transfers in a burst. This
information determines the number of data transfers associated with the address.
This changes between AXI3 and AXI4. See _Burst length_ on page A3-46 .

**AWSIZE** Master Burst size. This signal indicates the size of each transfer in the burst. See _Burst size_
on page A3-47 .

**AWBURST** Master Burst type. The burst type and the size information, determine how the address for
each transfer within the burst is calculated. See _Burst type_ on page A3-47 .

**AWLOCK** Master Lock type. Provides additional information about the atomic characteristics of the
transfer. This changes between AXI3 and AXI4.
See _Locked accesses_ on page A7-99 .

**AWCACHE** Master Memory type. This signal indicates how transactions are required to progress
through a system. See _Memory types_ on page A4-67 .

**AWPROT** Master Protection type. This signal indicates the privilege and security level of the
transaction, and whether the transaction is a data access or an instruction access.
See _Access permissions_ on page A4-73 .

**AWQOS** Master _Quality of Service_, QoS. The QoS identifier sent for each write transaction.
Implemented only in AXI4. See _QoS signaling_ on page A8-102 .

**AWREGION** Master Region identifier. Permits a single physical interface on a slave to be used for
multiple logical interfaces.
Implemented only in AXI4. See _Multiple region signaling_ on page A8-103 .

**AWUSER** Master User signal. Optional User-defined signal in the write address channel.
Supported only in AXI4. See _User-defined signaling_ on page A8-104 .

**AWVALID** Master Write address valid. This signal indicates that the channel is signaling valid write
address and control information. See _Channel handshake signals_ on page A3-40 .

**AWREADY** Slave Write address ready. This signal indicates that the slave is ready to accept an
address and associated control signals. See _Channel handshake signals_ on
page A3-40 .


-----

**A2.3** **Write data channel signals**

Table A2-3 shows the AXI write data channel signals. Unless the description indicates otherwise, a signal is used
by AXI3 and AXI4.

**Table A2-3 Write data channel signals**

**Signal** **Source** **Description**

**WID** Master Write ID tag. This signal is the ID tag of the write data transfer. Supported only in AXI3.
See _Transaction ID_ on page A5-79 .

**WDATA** Master Write data.

**WSTRB** Master Write strobes. This signal indicates which byte lanes hold valid data. There is one write
strobe bit for each eight bits of the write data bus. See _Write strobes_ on page A3-52 .

**WLAST** Master Write last. This signal indicates the last transfer in a write burst. See _Write data channel_
on page A3-41 .

**WUSER** Master User signal. Optional User-defined signal in the write data channel.
Supported only in AXI4. See _User-defined signaling_ on page A8-104 .

**WVALID** Master Write valid. This signal indicates that valid write data and strobes are available. See
_Channel handshake signals_ on page A3-40 .

**WREADY** Slave Write ready. This signal indicates that the slave can accept the write data. See _Channel_
_handshake signals_ on page A3-40 .


-----

**A2.4** **Write response channel signals**

Table A2-4 shows the AXI write response channel signals. Unless the description indicates otherwise, a signal is
used by AXI3 and AXI4.

**Table A2-4 Write response channel signals**

**Signal** **Source** **Description**

**BID** Slave Response ID tag. This signal is the ID tag of the write response. See _Transaction ID_ on
page A5-79 .

**BRESP** Slave Write response. This signal indicates the status of the write transaction. See _Read and_
_write response structure_ on page A3-57 .

**BUSER** Slave User signal. Optional User-defined signal in the write response channel. Supported only
in AXI4. See _User-defined signaling_ on page A8-104 .

**BVALID** Slave Write response valid. This signal indicates that the channel is signaling a valid write
response. See _Channel handshake signals_ on page A3-40 .

**BREADY** Master Response ready. This signal indicates that the master can accept a write response. See
_Channel handshake signals_ on page A3-40 .


-----

**A2.5** **Read address channel signals**

Table A2-5 shows the AXI read address channel signals. Unless the description indicates otherwise, a signal is used
by AXI3 and AXI4.

**Table A2-5 Read address channel signals**

**Signal** **Source** **Description**

**ARID** Master Read address ID. This signal is the identification tag for the read address group of
signals. See _Transaction ID_ on page A5-79 .

**ARADDR** Master Read address. The read address gives the address of the first transfer in a read burst
transaction. See _Address structure_ on page A3-46 .

**ARLEN** Master Burst length. This signal indicates the exact number of transfers in a burst. This
changes between AXI3 and AXI4. See _Burst length_ on page A3-46 .

**ARSIZE** Master Burst size. This signal indicates the size of each transfer in the burst. See _Burst size_ on
page A3-47 .

**ARBURST** Master Burst type. The burst type and the size information determine how the address for each
transfer within the burst is calculated. See _Burst type_ on page A3-47 .

**ARLOCK** Master Lock type. This signal provides additional information about the atomic characteristics
of the transfer. This changes between AXI3 and AXI4. See _Locked accesses_ on
page A7-99 .

**ARCACHE** Master Memory type. This signal indicates how transactions are required to progress through
a system. See _Memory types_ on page A4-67 .

**ARPROT** Master Protection type. This signal indicates the privilege and security level of the transaction,
and whether the transaction is a data access or an instruction access. See _Access_
_permissions_ on page A4-73 .

**ARQOS** Master _Quality of Service_, QoS. QoS identifier sent for each read transaction. Implemented
only in AXI4. See _QoS signaling_ on page A8-102 .

**ARREGION** Master Region identifier. Permits a single physical interface on a slave to be used for multiple
logical interfaces. Implemented only in AXI4. See _Multiple region signaling_ on
page A8-103 .

**ARUSER** Master User signal. Optional User-defined signal in the read address channel.
Supported only in AXI4. See _User-defined signaling_ on page A8-104 .

**ARVALID** Master Read address valid. This signal indicates that the channel is signaling valid read
address and control information. See _Channel handshake signals_ on page A3-40 .

**ARREADY** Slave Read address ready. This signal indicates that the slave is ready to accept an address
and associated control signals. See _Channel handshake signals_ on page A3-40 .


-----

**A2.6** **Read data channel signals**

Table A2-6 shows the AXI read data channel signals. Unless the description indicates otherwise, a signal is used by
AXI3 and AXI4.

**Table A2-6 Read data channel signals**

**Signal** **Source** **Description**

**RID** Slave Read ID tag. This signal is the identification tag for the read data group of signals
generated by the slave. See _Transaction ID_ on page A5-79 .

**RDATA** Slave Read data.

**RRESP** Slave Read response. This signal indicates the status of the read transfer. See _Read and write_
_response structure_ on page A3-57 .

**RLAST** Slave Read last. This signal indicates the last transfer in a read burst. See _Read data channel_ on
page A3-41 .

**RUSER** Slave User signal. Optional User-defined signal in the read data channel.
Supported only in AXI4. See _User-defined signaling_ on page A8-104 .

**RVALID** Slave Read valid. This signal indicates that the channel is signaling the required read data. See
_Channel handshake signals_ on page A3-40 .

**RREADY** Master Read ready. This signal indicates that the master can accept the read data and response
information. See _Channel handshake signals_ on page A3-40 .


-----

**A2.7** **Low-power interface signals**

Table A2-7 shows the signals of the optional low-power interface. These signals are used by the AXI3 and AXI4
protocols.

**Table A2-7 Low-power interface signals**

**Signal** **Source** **Description**

**CSYSREQ** Clock controller System exit low-power state request. This signal is a request from the system
clock controller for the peripheral to exit from a low-power state. See
_Power-down or power-up handshake_ on page A9-107 .

**CSYSACK** Peripheral device Exit low-power state acknowledgement. This signal is the acknowledgement
from a peripheral to a system exit low-power state request. See _Power-down or_
_power-up handshake_ on page A9-107 .

**CACTIVE** Peripheral device Clock active. This signal indicates that the peripheral requires its clock signal.
See _Peripheral clock required_ on page A9-107 .


-----

# Part B

### AMBA AXI4-Lite Interface Specification


-----

-----

## Chapter B1 AMBA AXI4-Lite

This chapter defines the AXI4-Lite interface and associated protocol. AXI4-Lite is suitable for simpler control
register-style interfaces that do not require the full functionality of AXI4.

This chapter contains the following sections:

-  _Definition of AXI4-Lite_ on page B1-126

-  _Interoperability_ on page B1-128

-  _Defined conversion mechanism_ on page B1-129

-  _Conversion, protection, and detection_ on page B1-131 .


-----

**B1.1** **Definition of AXI4-Lite**

This section defines the functionality and signal requirements of AXI4-Lite components.

The key functionality of AXI4-Lite operation is:

-  all transactions are of burst length 1

-  all data accesses use the full width of the data bus

— AXI4-Lite supports a data bus width of 32-bit or 64-bit.

-  all accesses are Non-modifiable, Non-bufferable

-  Exclusive accesses are not supported.

**B1.1.1** **Signal list**

Table B1-1 shows the required signals on an AXI4-Lite interface.

**Table B1-1 AXI4-Lite interface signals**

**Write address** **Write data** **Write response** **Read address** **Read data**
**Global**
**channel** **channel** **channel** **channel** **channel**

**ACLK** **AWVALID** **WVALID** **BVALID** **ARVALID** **RVALID**

**ARESETn** **AWREADY** **WREADY** **BREADY** **ARREADY** **RREADY**

− **AWADDR** **WDATA** **BRESP** **ARADDR** **RDATA**

− **AWPROT** **WSTRB** − **ARPROT** **RRESP**

**AXI4 signals modified in AXI4-Lite**

The AXI4-Lite interface does not fully support the following signals:

**RRESP, BRESP**

The EXOKAY response is not supported on the read data and write response channels.

**AXI4 signals not supported in AXI4-Lite**

The AXI4-Lite interface does not support the following signals:

**AWLEN, ARLEN** The burst length is defined to be 1, equivalent to an **AxLEN** value of zero.

**AWSIZE, ARSIZE** All accesses are defined to be the width of the data bus.

**Note**

AXI4-Lite requires a fixed data bus width of either 32-bit or 64-bit.

**AWBURST, ARBURST**

The burst type has no meaning because the burst length is 1.

**AWLOCK, ARLOCK**

All accesses are defined as Normal accesses, equivalent to an **AxLOCK** value of zero.

**AWCACHE, ARCACHE**

All accesses are defined as Non-modifiable, Non-bufferable, equivalent to an **AxCACHE**
value of 0b0000 .


-----

**WLAST, RLAST** All bursts are defined to be of length 1, equivalent to a **WLAST** or **RLAST** value of 1.

**B1.1.2** **Bus width**

AXI4-Lite has a fixed data bus width and all transactions are the same width as the data bus. The data bus width
must be, either 32-bits or 64-bits.

ARM expects that:

-  the majority of components use a 32-bit interface

-  only components requiring 64-bit atomic accesses use a 64-bit interface.

A 64-bit component can be designed for access by 32-bit masters, but the implementation must ensure that the
component sees all transactions as 64-bit transactions.

**Note**

This interoperability can be achieved by including, in the register map of the component, locations that are suitable
for access by a 32-bit master. Typically, such locations would use only the lower 32-bits of the data bus.

**B1.1.3** **Write strobes**

The AXI4-Lite protocol supports write strobes. This means multi-sized registers can be implemented and also
supports memory structures that require support for 8-bit and 16-bit accesses.

All master interfaces and interconnect components must provide correct write strobes.

Any slave component can choose whether to use the write strobes. The options permitted are:

-  to make full use of the write strobes

-  to ignore the write strobes and treat all write accesses as being the full data bus width

-  to detect write strobe combinations that are not supported and provide an error response.

A slave that provides memory access must fully support write strobes. Other slaves in the memory map might
support a more limited write strobe option.

When converting from full AXI to AXI4-Lite, a write transaction can be generated on AXI4-Lite with all write
strobes deasserted. Automatic suppression of such transactions is permitted but not required. See _Conversion,_
_protection, and detection_ on page B1-131 .

**B1.1.4** **Optional signaling**

AXI4-Lite supports multiple outstanding transactions, but a slave can restrict this by the appropriate use of the
handshake signals.

AXI4-Lite does not support AXI IDs. This means all transactions must be in order, and all accesses use a single
fixed ID value.

**Note**

Optionally, an AXI4-Lite slave can support AXI ID signals, so that it can be connected to a full AXI interface
without modification. See _Interoperability_ on page B1-128 .

AXI4-Lite does not support data interleaving, the burst length is defined as 1.


-----

**B1.2** **Interoperability**

This section describes the interoperability of AXI and AXI4-Lite masters and slaves. Table B1-2 shows the possible
combinations of interface, and indicates that the only case requiring special consideration is an AXI master
connecting to an AXI4-Lite slave.

**Table B1-2 Full AXI and AXI4-Lite interoperability**

**Master** **Slave** **Interoperability**

AXI AXI Fully operational.

AXI AXI4-Lite AXI ID reflection is required. Conversion might be required.

AXI4-Lite AXI Fully operational.

AXI4-Lite AXI4-Lite Fully operational.

**B1.2.1** **Bridge requirements of AXI4-Lite slaves**

As Table B1-2 shows, the only interoperability case that requires special consideration is the connection of an
AXI4-Lite slave interface to a full AXI master interface.

This connection requires AXI ID reflection. The AXI4-Lite slave must return the AXI ID associated with the
address of a transaction with the read data or write response for that transaction. This is required because the master
requires the returning ID to correctly identify the transaction response.

If an implementation cannot ensure that the AXI master interface only generates transactions in the AXI4-Lite
subset, then some form of adaptation is required. See _Conversion, protection, and detection_ on page B1-131 .

**B1.2.2** **Direct connection requirements of AXI4-Lite slaves**

An AXI4-Lite slave can be designed to include ID reflection logic. This means the slave can be used directly on a
full AXI connection, without a bridge function, in a system that guarantees that the slave is accessed only by
transactions that comply with the AXI4-Lite subset.

**Note**

This specification recommends that the ID reflection logic uses **AWID**, instead of **WID**, to ensure compatibility
with both AXI3 and AXI4.


-----

**B1.3** **Defined conversion mechanism**

This section defines the requirements to convert any legal AXI transaction for use on an AXI4-Lite component.
_Conversion, protection, and detection_ on page B1-131 discusses the advantages and disadvantages of the various
approaches that can be used.

**B1.3.1** **Conversion rules**

Conversion requires that the AXI data width is equal to or greater than the AXI4-Lite data width. If this is not the
case then the AXI data width must first be converted to the AXI4-Lite data width.

**Note**

AXI4-Lite does not support EXOKAY responses, so the conversion rules do not consider this response.

The rules for conversion from a full AXI interface are as follows:

-  If a transaction has a burst length greater than 1 then the burst is broken into multiple transactions of burst
length 1. The number of transactions that are created depends on the burst length of the original transaction.

-  When generating the address for subsequent beats of a burst, the conversion of bursts with a length greater
than 1 must take into consideration the burst type. An unaligned start address must be incremented and
aligned for subsequent beats of an INCR or WRAP burst. For a FIXED burst the same address is used for all
beats.

-  Where a write burst with length greater than 1 is converted into multiple write transactions, the component
responsible for the conversion must combine the responses for all of the generated transactions, to produce a
single response for the original burst. Any error response is sticky. That is, an error response received for any
of the generated transactions is retained, and the single combined response indicates an error. If both a
SLVERR and a DECERR are received then the first response received is the one that is used for the combined
response.

-  A transaction that is wider than the destination AXI4-Lite interface is broken into multiple transactions of the
same width as the AXI4-Lite interface. For transactions with an unaligned start address, the breaking up of
the burst occurs on boundaries that are aligned to the width of the AXI4-Lite interface.

-  Where a wide transaction is converted to multiple narrower transactions, the component responsible for the
conversion must combine the responses to all of the narrower transactions, to produce a single response for
the original transaction. Any error response is sticky. If both a SLVERR and a DECERR are received then
the first response received is used for the combined response.

-  Transactions that are narrower than the AXI4-Lite interface are passed directly and are not converted.

-  Write strobes are passed directly, unmodified.

-  Write transactions with no strobes are passed directly.

**Note**

The AXI4-Lite protocol does not require these transactions to be suppressed.

-  The **AxLOCK** signals are discarded for all transactions. For a sequence of locked transactions any lock
guarantee is lost. However, the locked nature of the transaction is lost only at any downstream arbitration.
For an exclusive sequence, the AXI signaling requirements mean any exclusive write access must fail.

-  The **AxCACHE** signals are discarded. All transactions are treated as Non-modifiable and Non-bufferable.

**Note**

This is acceptable because AXI permits Modifiable accesses to be treated as Non-modifiable, and Bufferable
accesses to be treated as Non-bufferable.

-  The **AxPROT** signals are passed directly, unmodified.


-----

The **WLAST** signal is discarded.

The **RLAST** signal is not required, and is considered asserted for every transfer on the read data channel.


-----

**B1.4** **Conversion, protection, and detection**

Connection of an AXI4-Lite slave to an AXI4 master requires some form of adaptation if it can not be ensured that
the master only issues transactions that meet the AXI4-Lite requirements.

This section describes techniques that can be adopted in a system design to aid with the interoperability of
components and the debugging of system design problems. These techniques are:

**Conversion** This requires the conversion of all transactions to a format that is compatible with the AXI4-Lite
requirements.

**Protection** This requires the detection of any non-compliant transaction. The non-compliant transaction is
discarded, and an error response is returned to the master that generated the transaction.

**Detection** This requires observing any transaction that falls outside the AXI4-Lite requirements and:

-  notifying the controlling software of the unexpected access

-  permitting the access to proceed at the hardware interface level.

**B1.4.1** **Conversion and protection levels**

Different levels of conversion and protection can be implemented:

**Full conversion**

This converts all AXI transactions, as described in _Defined conversion mechanism_ on page B1-129 .

**Simple conversion with protection**

This propagates transactions that only require a simple conversion, but suppresses and error reports
transactions that require a more complex task.

Examples of transactions that are propagated are the discarding of one or more of **AxLOCK** and
**AxCACHE** .

Examples of transactions that are discarded and generate an error report are burst length or data
width conversions.

**Full protection**

Suppress and generate an error for every transaction that does not comply with the AXI4-Lite
requirements.

**B1.4.2** **Implementation considerations**

A protection mechanism that discards transactions must provide a protocol-compliant error response to prevent
deadlock. For example, in the full AXI protocol, read burst transactions require an error for each beat of the burst
and a correctly asserted **RLAST** signal.

Using a combination of detection and conversion permits hardware implementations that:

-  do not prevent unexpected accesses from occurring

-  provide a mechanism for notifying the controlling software of the unexpected access, so speeding up the
debug process.

In complex designs, the advantage of combining conversion and detection is that unforeseen future usage can be
supported. For example, at design time it might be considered that only the processor programs the control register
of a peripheral, but in practice, the peripheral might need to be programmed by other devices, for example a DSP
or a DMA controller, that cannot generate exactly the required AXI4-Lite access.

The advantages and disadvantages of the different approaches are:

-  Protection requires a lower gate count.
-
-  Conversion ensures the interface can operate with unforeseen accesses.

-  Conversion increases the portability of software from one system to another.


-----

Conversion might provide more efficient use of the AXI infrastructure. For example, a burst of writes to a
FIFO can be issued as a single burst, rather than needing to be issued as a set of single transactions.

Conversion might provide more efficient use of narrow links, where the address and data payload signals are
shared.

Conversion might provide more flexibility in components that can be placed on AXI4-Lite interfaces. By
converting bursts and permitting sparse strobes, memory can be placed on AXI4-Lite, with no burst
conversion required in the memory device. This is, essentially, a sharing of the burst conversion logic.


-----

