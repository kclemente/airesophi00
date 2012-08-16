import java.util.ArrayList;
import java.util.Iterator;
import java.util.Enumeration;
import java.io.PrintStream;
import java.lang.reflect.Method;
import java.util.Hashtable;
import java.lang.Integer;
import java.util.concurrent.locks.Lock;
import java.util.concurrent.locks.ReentrantLock;
/**
 * <pre>
 * Node -- Class defining the data structures and code for the
 * protocol stack for a node participating in the fishnet

 * This code is under student control; we provide a baseline
 * "hello world" example just to show how it interfaces with the FishNet classes.
 *
 * NOTE: per-node global variables are prohibited.
 *  In simulation mode, we execute many nodes in parallel, and thus
 *  they would share any globals.  Please put per-node state in class Node
 *  instead.
 *
 * In other words, all the code defined here should be generic -- it shouldn't
 * matter to this code whether it is executing in a simulation or emulation
 *
 * This code must be written as a state machine -- each upcall must do its work and return so that
 * other upcalls can be delivered
 * </pre>
 */

public class Node {
	// Timeout pings in 10 seconds
    private final long PingTimeout = 10000;  
    
    // Fishnet manager. Has functions Node uses to communicate
    // with network...
    private Manager manager;
    
    // Node address...
    private int addr;
    private String naddr;
    // Sequence Number, for both packets and link states:
    private int seqNum;
    private int LseqNum;
    // integer used to keep track of connected neighbors
    private int nCount;
    
    // To store PingRequests.
    private ArrayList pings; 

    // To keep track of all the packets we have already flooded.
    // The first Integer represents a source address, and the
    // second integer represents the last packet sent from that
    // node with the largest seqNum.
    private Hashtable <Integer, Integer> flooded;
    
    // Hashtables to be used for Link State packets:
    private Hashtable <Integer, Integer> lsrec;
    private Hashtable <Integer, LinkState> lsrecv;
    private Hashtable <Integer, Integer> lsttl;
    
    private Hashtable <Integer, String> lsname;
    private Hashtable <Integer, Integer> lsnameseq;
    
    // Hashtables to be used for routing:
    private Hashtable <Integer, Integer> destHop;
    private Hashtable <Integer, Integer> destCost;
    
    // To keep track of all packets received:
    private ArrayList <Integer> recWindow;
    
    // To keep track of all the node's neighbors:
    private Hashtable <Integer, Integer> neighborList;
    
    // locks for mutual exclusion:
    // Neighbor List lock:
    private final Lock mtx = new ReentrantLock();
    // Link state lock:
    private final Lock lsmtx = new ReentrantLock();
    // Routing table lock:
    private final Lock rtmtx = new ReentrantLock();
    // Lock for the name packets:
    private final Lock npmtx = new ReentrantLock();
    // Fishnet reliable data transfer
    // TCP manager
    private TCPManager tcpMan;

    /**
     * Create a new node
     * @param manager The manager that is managing Fishnet
     * @param addr The address of this node
     */
    public Node(Manager manager, int addr) {
		this.manager = manager;
		this.addr = addr;
		this.pings = new ArrayList();
		
		// Initialize all the needed hash tables or array lists:
		this.flooded = new Hashtable <Integer, Integer>();
		this.lsrec = new Hashtable <Integer, Integer>();
		this.lsrecv = new Hashtable <Integer, LinkState>();
		this.lsttl = new Hashtable <Integer, Integer>();
		this.lsname = new Hashtable <Integer, String>();
		this.lsnameseq = new Hashtable <Integer, Integer>();
		this.destHop = new Hashtable <Integer, Integer>();
		this.destCost = new Hashtable <Integer, Integer>();
		
		this.naddr = "" + this.addr;
		this.seqNum = 0;
		this.LseqNum = 0;
		this.nCount = 0;
		this.recWindow = new ArrayList <Integer> ();
		this.neighborList = new Hashtable <Integer, Integer> ();
		// Add this node's address to the hash table:
		flooded.put(this.addr, -1);
		
        // Fishnet reliable data transfer
        this.tcpMan = new TCPManager(this, addr, manager);
    }

    /**
     * Called by the manager to start this node up.
     */
    public void start() {
    	// Set LseqNum to zero, or reset to zero if it's a re-start.
    	this.LseqNum = 0;
		logOutput("started");
		this.addTimer(PingTimeout, "pingTimedOut");
	
        // Fishnet reliable data transfer
        // Start TCP manager
        tcpMan.start();
        this.findNeighbors();
        this.neighborDetection();
    }

    /**
     * Called by the manager when a packet has arrived for this node
     * @param from The address of the node that has sent this packet
     * @param msg The serialized form of the packet.
     */
    public void onReceive(Integer from, byte[] msg) {
		Packet packet = Packet.unpack(msg);
		//logOutput("received packet from " + from);
		if(packet == null) {
		    logError("Unable to unpack message: " + Utility.byteArrayToString(msg) + " Received from " + from);
		    return;
		}
		this.receivePacket(from.intValue(), packet);
    }

    /**
     * Called by the manager when there is a command for this node from the user.
     * Command can be input either from keyboard or file.
     * For now sending messages as ping to a neighbor.
     * @param command The command for this node
     */
    public void onCommand(String command) {
    	if(this.matchLS(command)){
    		return;
    	}
    	if(this.matchListUsers(command)){
    		return;
    	}
    	if(this.matchHello(command)){
    		return;
    	}
    	if(this.matchCommands(command)){
    		return;
    	}
    	if(this.matchDumpTable(command)){
    		return;
    	}
    	if(this.matchTransfer(command)){
    		return;
    	}
    	if(this.matchDumpNeighbors(command)){
			return;
		}
    	if(this.matchDumpLinkState(command)){
    		return;
    	}
    	if(this.matchNameChange(command)){
			return;
		}
        if (this.matchTransferCommand(command)) {
            return;
        }

        if (this.matchServerCommand(command)) {
            return;
        }

		if(this.matchPingCommand(command)) {
		    return;
		}
		logError("Unrecognized command: " + command);
    }

    /**
     * Callback method given to manager to invoke when a timer fires.
     */
    public void pingTimedOut() {
		Iterator iter = this.pings.iterator();
		while(iter.hasNext()) {
		    PingRequest pingRequest = (PingRequest)iter.next();
		    
		    if((pingRequest.getTimeSent() + PingTimeout) < this.manager.now()) {
				try {
				    logOutput("Timing out ping: " + pingRequest);
				    iter.remove();
				}catch(Exception e) {
				    logError("Exception occured while trying to remove an element " +
				    		"from ArrayList pings.  Exception: " + e);
				    return;
				}
		    }
		    
		}
		
		this.addTimer(PingTimeout, "pingTimedOut");
    }
    /* 
     * Periodically floods neighbor-discovery packets to its neighbors.
     * */
    public void findNeighbors(){
    		mtx.lock();
    		try{
	    		if(nCount == Integer.MAX_VALUE)
	    			nCount = 0;
	    		else
	    			nCount++;
    		} finally{
    			mtx.unlock();
    		}
    		String body = "Hello neighbor!";
    		Packet packet = new Packet(this.addr, this.addr, 1, 
    				Protocol.PING_PKT, seqNum, Utility.stringToByteArray(body)); 
    		seqNum++;
    		this.send(this.addr, packet);
    		this.addTimer(10000, "findNeighbors");
    }
    /*
     * The function to determine this node's neighbors.
     * nCount = increments by one every time this node sends out neighbor
     * discovery packets. As this node receives neighbor discovery ping
     * replies, those ping replies' sender addresses will be registered
     * along with the current nCount. Basically, a neighbor is considered
     * to be present if: 
     * (node's current nCount) - (ping reply's nCount when it's processed) <= 3
     * 
     * if that difference exceeds 3, that means that the neighbor has failed to
     * send a ping reply 3 times already, and will be considered absent.
     * */
    public void neighborDetection(){
    	// Contains this nodes neighbors; will be sent out in LinkState advertisements
	    ArrayList <Integer> LSN = new ArrayList <Integer> ();
	    mtx.lock();
	    try{
		    Enumeration <Integer> trvrs = neighborList.keys();
		    while(trvrs.hasMoreElements()){
		    	Integer x = trvrs.nextElement();
			    if(Math.abs(nCount - neighborList.get(x)) <= 3){
			   		LSN.add(x);
			   	} 
		    }
		    // Convert LSN to a primitive integer array, to pass to LinkState
		    Iterator <Integer> FD = LSN.iterator();
		    int [] neighArray = new int [LSN.size()];
		    int count = 0;
		    while(FD.hasNext()){
		    	neighArray[count] = FD.next();
		    	count++;
		    }
		    LinkState lstate = new LinkState(neighArray);
		    // Every time this function is called, decrement each LinkState packet's
		    // TTL by one. However, in our Hashtables of LinkState packets, update this
		    // node's information.
		    lsmtx.lock();
		    try{
		    	this.decreaseLSTTL();
		    	this.lsrecv.put(this.addr, lstate);
				this.lsrec.put(this.addr, this.LseqNum);
				this.lsttl.put(this.addr, 3);
		    }finally{
		    	lsmtx.unlock();
		    }
		    // For now, periodically send out Link State and Name packets, then LseqNum++
		    Packet packet = new Packet(this.addr, this.addr, Packet.MAX_TTL,
		    			Protocol.LINK_INFO_PKT, LseqNum, lstate.pack());
		    npmtx.lock();
		    try{
			    Packet npacket = new Packet(this.addr, this.addr, Packet.MAX_TTL,
			    			Protocol.NAME_PKT, LseqNum, Utility.stringToByteArray(this.naddr));
			    this.send(this.addr, npacket);
		    }finally{
		    	npmtx.unlock();
		    }
		    LseqNum++;
		    this.send(this.addr, packet);
		    
	    } finally{
	    	mtx.unlock();
	    }
    	this.addTimer(45000, "neighborDetection");
    	this.addTimer(175000, "calcRouteTable");
    }
    // Timer-based function to periodically calculate Dijkstra...?
    public void calcRouteTable(){
    	this.useDijkstra();
    	this.addTimer(75000, "calcRouteTable");
    }
    // Function used to list all nodes in the network:
    private boolean matchLS(String command){
    	String[] args = command.split(" ");
        if (args.length != 1 || !args[0].equals("ls")){
            return false;
        }
        lsmtx.lock();
        try{
	        Enumeration <Integer> trvrs = lsrecv.keys();
	        this.logOutput("Nodes currently present in the network...");
	        while(trvrs.hasMoreElements()){
	        	Integer x = trvrs.nextElement();
	        	if(lsttl.get(x) > 0){
	        		this.logOutput("Node " + lsname.get(x));
	        	}
	        }
        }finally{
        	lsmtx.unlock();
        }
        return true;
    }
    private boolean matchTransfer(String command){
    	String[] args = command.split(" ");
        if (args.length != 2 || !args[0].equals("transfer")){
            return false;
        }
        try{
	        int destAddr = Integer.parseInt(args[1]);
	        // Setting up connection with other node:
	    	// int port = tcpMan.reqPort(this.addr, destAddr);
        }catch(Exception e){
        	logError("Exception: " + e);
        }
        return true;
    }
    //Format: hello <username> <src port> <dest addr>\r\n
    private boolean matchHello(String command){
    	String[] args = command.split(" ");
    	if(args.length != 4 || !args[0].equals("hello")){
    		return false;
    	}
    	String ftcom = "hello " + args[1] + " " + args[2] + "\r\n";
    	tcpMan.initConnection(Integer.parseInt(args[2]), Integer.parseInt(args[3]), 88, 0, 
    			FishtankClient.DEFAULT_CLIENT_INTERVAL, 
    			FishtankClient.DEFAULT_BUFFER_SZ, args[1], ftcom);
    	return true;
    }
    private boolean matchCommands(String command){
    	String[] args = command.split(" ");
    	if(!args[0].equals("message")){
    		return false;
    	}
    	String ftcom = "";
    	for(int i = 0; i < args.length; i++){
    		ftcom = ftcom + args[i] + " ";
    	}
    	//logOutput("ftcom is " + ftcom);
    	tcpMan.sendCommands(ftcom);
    	return true;
    }
    private boolean matchListUsers(String command){
    	String[] args = command.split(" ");
    	if(args.length < 1 || !args[0].equals("listusers")){
    		return false;
    	}
    	tcpMan.sendCommands("listusers" + " " + "listusers\r\n");
    	return true;
    }
    // Function used to change this node's name:
    private boolean matchNameChange(String command){
    	String[] args = command.split(" ");
        if (args.length < 2 || args.length > 4 || !args[0].equals("changename")){
            return false;
        }
    	npmtx.lock();
    	try{
    		this.naddr = args[1];
    	}finally{
    		npmtx.unlock();
    	}
    	return true;
    }
    // Simply prints out the routing table produced by Dijkstra:
    private boolean matchDumpTable(String command){
    	String[] args = command.split(" ");
        if (args.length < 2 || args.length > 4 || !args[0].equals("dump") || !args[1].equals("table")) {
            return false;
        }
        rtmtx.lock();
        try{
        	this.logOutput("Routing table is...");
        	Enumeration <Integer> trvrs = this.destHop.keys();
        	while(trvrs.hasMoreElements()){
        		Integer x = trvrs.nextElement();
        		this.logOutput("Dest: " + lsname.get(x) + "\tNext hop: " + lsname.get(destHop.get(x)) 
        				+ "\tCost: " + destCost.get(x));
        	}
        }finally{
        	rtmtx.unlock();
        }
        return true;
    }
    /* The "dump neighbors" command that will print nodes'
     * neighbors. Only prints the neighbors that are currently present.
     * See documentation of findNeighbors() to see how node determines
     * present neighbors.
     * */
    private boolean matchDumpNeighbors(String command){
    	String[] args = command.split(" ");
        if (args.length < 2 || args.length > 4 || !(args[0].equals("dump") && args[1].equals("neighbors")) ) {
            return false;
        }
    	Enumeration <Integer> trvrs = neighborList.keys();
      
	    this.logOutput("Neighbors are...");
	   	while(trvrs.hasMoreElements()){
	   		Integer x = trvrs.nextElement();
	   		if(nCount - neighborList.get(x) <= 3){
	   			npmtx.lock();
	   			try{
	   				this.logOutput("Node " + this.addr + " <--> Node " + lsname.get(x));
	   			}finally{
	   				npmtx.unlock();
	   			}
	   		} 
	   	}
    	return true;
    }
    
    private boolean matchDumpLinkState(String command){
    	String[] args = command.split(" ");
        if (args.length < 2 || args.length > 4 || !args[0].equals("dump") || !args[1].equals("linkstate")) {
            return false;
        }
        lsmtx.lock();
        try{
	        Enumeration <Integer> trvrs = lsrecv.keys();
	        this.logOutput("Has Link State advertisements from...");
	        while(trvrs.hasMoreElements()){
	        	Integer x = trvrs.nextElement();
	        	if(lsttl.get(x) > 0){
	        		this.logOutput("Node " + lsname.get(x));
	        	}
	        }
        }finally{
        	lsmtx.unlock();
        }
        return true;
    }
   
    private boolean matchPingCommand(String command) {
		int index = command.indexOf(" ");
		if(index == -1) {
		    return false;
		}
		try {
			String dStr = command.substring(0,index);
			int destAddr = this.nameTranslate(dStr);
		    //int destAddr = Integer.parseInt(command.substring(0, index));
			if(destAddr < 0){
				logOutput("No such destination address exists!");
				return true;
			}
		    String message = command.substring(index+1);
		    Packet packet = new Packet(destAddr, this.addr, Packet.MAX_TTL, Protocol.PING_PKT, seqNum,
					       Utility.stringToByteArray(message));
		    seqNum++;
		    this.send(destAddr, packet);
		    this.pings.add(new PingRequest(destAddr, Utility.stringToByteArray(message), this.manager.now()));
		    return true;
		}catch(Exception e) {
		    logError("Exception: " + e);
		}
	
		return false;
    }
    
    /** Called by manager to receive packets.
     *  K: I guess this is where packet-type compatibility is implemented
     *  but only use Packet info accessible from Packet.java!
     * @param from
     * @param packet
     */
    private void receivePacket(int from, Packet packet) {
    	/*
    	 * Record the source of this packet, as first step in flood control.
    	 * -1 indicates that we have not sent packets from this addr yet.
    	*/
    	if( !flooded.containsKey(packet.getSrc()) ){
			flooded.put(packet.getSrc(), -1);
		}
    	// Decrement packet's TTL since it was sent successfully.
		packet.setTTL(packet.getTTL() - 1);
		
    	// Switch statement, to deal with different types of packets:
		switch(packet.getProtocol()) {
			case Protocol.PING_PKT:
			    this.receivePing(packet);
			    break;
			case Protocol.TRANSPORT_PKT:
				this.receiveTransportPacket(packet);
				break;
			case Protocol.NAME_PKT:
				this.receiveNamePacket(packet);
				break;
			case Protocol.PING_REPLY_PKT:
			    this.receivePingReply(packet);
			    break;
			case Protocol.LINK_INFO_PKT:
				this.receiveLinkState(packet);
				break;
			default:
			    logError("Packet with unknown protocol received. Protocol: " + packet.getProtocol());
		}
    }
    /** The function called when node receives a transport packet:
     *  */
    private void receiveTransportPacket(Packet packet){
    	try{
    		if(packet.getSrc() == this.addr){
    			return;
    		}
    		// Only process this ping packet if it's addressed to this node:
			if(packet.getDest() == this.addr){
				// Make sure it doesn't process the same packet twice by checking if
				// we have already processed this sequence number.
				if(recWindow.contains(packet.getSeq()) ){
		    		return;
		    	}
				// Print message, notifying user that a packet addressed to it is received:
				/*
				npmtx.lock();
				try{
					logOutput("Received TCP packet from " + lsname.get(packet.getSrc()));
				}finally{
					npmtx.unlock();
				}*/
		    	recWindow.add(packet.getSeq());
		    	// Send to TCP manager...?
		    	tcpMan.receivePacket(packet);
			}
			// Else, just forward it.
			else{
				this.send(packet.getDest(), packet);
			}
    		
    	}catch(IllegalArgumentException e){
    		logError("Exception while processing a Transport packet. Exception: " + e);
    	}
    }
    /** The function that is called when node recieves a Link State packet
     * 
     */
    private void receiveNamePacket(Packet packet){
    	try{
    		// If this node receives its own Name packet, ignore it.
    		if(packet.getSrc() == this.addr){
    			return;
    		}
    		// If the Name packet received is not in our collection yet, add it.
    		if(!lsname.containsKey(packet.getSrc())){
    			npmtx.lock();
    			try{
	    			String x = Utility.byteArrayToString(packet.getPayload());
	    			lsname.put(packet.getSrc(), x);
	    			lsnameseq.put(packet.getSrc(), packet.getSeq());
	    			lsname.put(this.addr, this.naddr);
    				lsnameseq.put(this.addr, packet.getSeq());
    			}finally{
    				npmtx.unlock();
    			}
    		}
    		// Else, only add it if it has a higher sequence number than what we currently
    		// have stored.
    		else{
    			if(packet.getSeq() <= lsnameseq.get(packet.getSrc())){
    				return;
    			}
	    		npmtx.lock();
	    		try{
	    			String x = Utility.byteArrayToString(packet.getPayload());
	    			lsname.put(packet.getSrc(), x);
	    			lsnameseq.put(packet.getSrc(), packet.getSeq());
	    			lsname.put(this.addr, this.naddr);
    				lsnameseq.put(this.addr, packet.getSeq());
	    		}finally{
	    			npmtx.unlock();
	    		}
    		}
    		this.send(packet.getSrc(), packet);
    	}catch(IllegalArgumentException e){
    		logError("Exception while processing a Name packet. Exception: " + e);
    	}
    }
    private void receiveLinkState(Packet packet){
    	try{
    		// If this node receives its own LinkState packet, ignore it.
    		if(packet.getSrc() == this.addr){
    			return;
    		}
    		// If the LSP received is not in our collection yet, add it.
    		if(!lsrec.containsKey(packet.getSrc())){
    			lsmtx.lock();
    			try{
    				//logOutput("Received Link-State packet from " + packet.getSrc());
    				lsrec.put(packet.getSrc(), packet.getSeq());
        			lsrecv.put(packet.getSrc(), LinkState.unpack(packet.getPayload()));
    				lsttl.put(packet.getSrc(), 3);
    			}finally{
    				lsmtx.unlock();
    			}
    			this.send(packet.getSrc(), packet);
    		}
    		// Else, only add it if it has a higher sequence number than what we currently
    		// have stored.
    		else{
    			if(packet.getSeq() <= lsrec.get(packet.getSrc())){
    				return;
    			}
    			else{
    				lsmtx.lock();
        			try{
        				//logOutput("Received Link-State packet from " + packet.getSrc());
        				lsrec.put(packet.getSrc(), packet.getSeq());
        				lsrecv.put(packet.getSrc(), LinkState.unpack(packet.getPayload()));
        				lsttl.put(packet.getSrc(), 3);
        			}finally{
        				lsmtx.unlock();
        			}
    				this.send(packet.getSrc(), packet);
    			}
    		}
    	}catch(IllegalArgumentException e){
    		logError("Exception while trying to send a Link State packet. Exception: " + e);
    	}
    }
    /** The function that is called when node receives a Ping packet
     * 
     * @param packet
     */
    private void receivePing(Packet packet) {
		try {
			// If TTL is zero, and source addr = dest addr, it is a neighbor call!
			if( (packet.getDest() == packet.getSrc()) && packet.getTTL() == 0){
				String body = Integer.toString(this.addr);
				int newSeq = flooded.get(packet.getSrc()) + 1;
				Packet reply = new Packet(packet.getSrc(), packet.getSrc(), 1, 
			    		Protocol.PING_REPLY_PKT, newSeq, Utility.stringToByteArray(body));
				this.send(reply.getDest(),reply);
			    return;
			}
			// Only process this ping packet if it's addressed to this node:
			if(packet.getDest() == this.addr){
				// Make sure it doesn't process the same packet twice by checking if
				// we have already processed this sequence number.
				if(recWindow.contains(packet.getSeq()) ){
		    		return;
		    	}
				// Print message, notifying user that a packet addressed to it is received:
				if((packet.getDest() != packet.getSrc()) && packet.getTTL() > 0){
					npmtx.lock();
					try{
						logOutput("Received Ping from " + lsname.get(packet.getSrc()) + " with message: " 
								+ Utility.byteArrayToString(packet.getPayload()));
					}finally{
						npmtx.unlock();
					}
				}
		    	recWindow.add(packet.getSeq());
		    	// Make a ping reply packet, send it back to proper address:
			    Packet reply = new Packet(packet.getSrc(), this.addr, Packet.MAX_TTL, 
			    		Protocol.PING_REPLY_PKT, seqNum, packet.getPayload());
			    this.seqNum++;
			    this.send(packet.getSrc(), reply);
			}
			// Else, just forward it.
			else{
				this.send(packet.getDest(), packet);
			}
		    
		}catch(IllegalArgumentException e) {
		    logError("Exception while trying to send a Ping Reply. Exception: " + e);
		}
    }

    /** Check that ping reply matches what was sent
     * 
     * @param packet
     */
    private void receivePingReply(Packet packet) {
    	/* 
    	 * Since ping replies are also flooded, do NOT process any ping replies this
    	 * node receives that is not intended for this node. Just forward them.
    	 */
    	if(packet.getDest() != this.addr){
    		this.send(packet.getDest(), packet);
    		return;
    	}
    	/* If packet's dest and src are the same, and its TTL is zero, it is a
    	 * neighbor discovery packet! Register the pingreply sender's ID into our
    	 * neighbors list!
    	 * */
    	if((packet.getDest() == packet.getSrc()) && packet.getTTL() == 0){
    		String IDS = Utility.byteArrayToString(packet.getPayload());
    		int ID = Integer.parseInt(IDS);
	    	mtx.lock();
	    	try{
	    		this.neighborList.put(ID, nCount);
	    	} finally{
	    		mtx.unlock();
	    	}
    		return;
    	}
    	
    	// Make sure it doesn't process the same packet twice:
		if(recWindow.contains(packet.getSeq()) ){
    		return;
    	}
    	recWindow.add(packet.getSeq());
    	
		Iterator iter = this.pings.iterator();
		String payload = Utility.byteArrayToString(packet.getPayload());
		while(iter.hasNext()) {
		    PingRequest pingRequest = (PingRequest)iter.next();
		    if( (pingRequest.getDestAddr() == packet.getSrc()) &&
			( Utility.byteArrayToString(pingRequest.getMsg()).equals(payload)) ){
		    	npmtx.lock();
		    	try{
		    		logOutput("Got Ping Reply from " + lsname.get(packet.getSrc()) + ": " + payload);
		    	}finally{
		    		npmtx.unlock();
		    	}
				try {
				    iter.remove();
				}catch(Exception e) {
				    logError("Exception occured while trying to remove an element from " +
				    		"ArrayList pings while processing Ping Reply.  Exception: " + e);
				}
				return;
		    }
		}
		logError("Unexpected Ping Reply from " + packet.getSrc() + ": " + payload);
    }
    
    /** Called by Manager to send packet to destination address
     * @param destAddr may or may not be used at the moment.
     * @param packet is the packet to be forwarded to destination.
     */
    private void send(int destAddr, Packet packet) {
		try {
			if(packet.getTTL() > 0){
				// Because these operate on a different seqNum...
				if( (packet.getProtocol() == Protocol.LINK_INFO_PKT) ||
						(packet.getProtocol() == Protocol.NAME_PKT) ){
					//if(packet.getProtocol() == Protocol.LINK_INFO_PKT){
					//	logOutput("Now flooding link-state packet...");
					//}
					this.manager.sendPkt(this.addr, Packet.BROADCAST_ADDRESS, packet.pack());
					return;
				}
				/*
				Only send packet if its seqNum is greater than the
				last seqNum registered to that packet's source addr.
				That indicates that this packet hasn't been flooded yet.
				Also, do NOT send this if TTL is already zero.
				*/
				if( ( packet.getSeq() > flooded.get(packet.getSrc()) ) &&
						(packet.getTTL() > 0) ){
					// Update this source addr's seqNum in the hash table, so that
					// this node will no longer send any packets with the same source
					// address that has a smaller seqNum:
					if(packet.getSrc() != packet.getDest()){
						flooded.put(packet.getSrc(), packet.getSeq());
					}
					// If this is a specialized discovery packet (source == destination), flood it.
					if( (packet.getSrc() == packet.getDest()) || (destAddr == Packet.BROADCAST_ADDRESS) ){
						this.manager.sendPkt(this.addr, Packet.BROADCAST_ADDRESS, packet.pack());
					}
					// Else, if destination is in routing table, route it.
					else if(destHop.containsKey(packet.getDest())){
						rtmtx.lock();
						try{
							npmtx.lock();
							try{
								//logOutput("Packet for Node " + lsname.get(packet.getDest()) + " ROUTED to Node "
								//		+ lsname.get(destHop.get(destAddr)));
							}finally{
								npmtx.unlock();
							}
							this.manager.sendPkt(this.addr, destHop.get(destAddr), packet.pack());
						}finally{
							rtmtx.unlock();
						}
					}
					// If destination is not in routing table, print out error.
					else{
						npmtx.lock();
						try{
							logOutput("Node " + lsname.get(packet.getDest()) + " is not in the routing table!");
						}finally{
							npmtx.unlock();
						}
						return;
					}
				}	
			}
			else{
				return;
			}
		}catch(IllegalArgumentException e) {
		    logError("Exception: " + e);
		}
    }

    // Adds a timer, to fire in deltaT milliseconds, with a callback to a public function 
    // of this class that takes no parameters
    private void addTimer(long deltaT, String methodName) {
		try {
		    Method method = Callback.getMethod(methodName, this, null);
		    Callback cb = new Callback(method, this, null);
		    this.manager.addTimer(this.addr, deltaT, cb);
		}catch(Exception e) {
		    logError("Failed to add timer callback. Method Name: " + methodName +
			     "\nException: " + e);
		}
    }

    // Fishnet reliable data transfer

    /**
     * Send a transport segment to the specified node (network layer service
     * entry point for the transport layer)
     *
     * @param srcAddr int Source node address
     * @param destAddr int Sestination node address
     * @param protocol int Transport layer protocol to use
     * @param payload byte[] Payload to be sent
     */
    public void sendSegment(int srcAddr, int destAddr, int protocol, byte[] payload) {
        Packet packet = new Packet(destAddr, srcAddr, Packet.MAX_TTL,
                                   protocol, seqNum, payload);
        this.seqNum++;
        this.send(destAddr, packet);
    }

    public int getAddr() {
        return this.addr;
    }

    public void logError(String output) {
    	this.log(output, System.err);
    }

    public void logOutput(String output) {
    	this.log(output, System.out);
    }

    private void log(String output, PrintStream stream) {
    	stream.println("Node " + this.addr + ": " + output);
    }

    private boolean matchTransferCommand(String command) {
        // transfer command syntax:
        //     transfer dest port localPort amount [interval sz]
        // Synopsis:
        //     Connect to a transfer server listening on port <port> at node
        //     <dest>, using local port <localPort>, and transfer <amount> bytes.
        // Required arguments:
        //     dest: address of destination node
        //     port: destination port
        //     localPort: local port
        //     amount: number of bytes to transfer
        // Optional arguments:
        //     interval: execution interval of the transfer client, default 1 second
        //     sz: buffer size of the transfer client, default 65536
        String[] args = command.split(" ");
        if (args.length < 5 || args.length > 7 || !args[0].equals("transfer")) {
            return false;
        }

        try {
            int destAddr = Integer.parseInt(args[1]);
            int port = Integer.parseInt(args[2]);
            int localPort = Integer.parseInt(args[3]);
            int amount = Integer.parseInt(args[4]);
            long interval =
                args.length >= 6 ?
                Integer.parseInt(args[5]) :
                TransferClient.DEFAULT_CLIENT_INTERVAL;
            int sz =
               args.length == 7 ?
               Integer.parseInt(args[6]) :
               TransferClient.DEFAULT_BUFFER_SZ;
            if(tcpMan.initConnection(localPort, destAddr, port, amount, interval,
            		sz) < 0){
            	logError("Port " + port + " is already binded to a socket.");
            }
            /*
            TCPSock sock = this.tcpMan.socket();
            sock.bind(localPort);
            sock.connect(destAddr, port);
            TransferClient client = new
                TransferClient(manager, this, sock, amount, interval, sz);
            client.start();
			*/
            return true;
        } catch (Exception e) {
            logError("Exception: " + e);
        }

        return false;
    }

    private boolean matchServerCommand(String command) {
        // server command syntax:
        //     server port backlog [servint workint sz]
        // Synopsis:
        //     Start a transfer server at the local node, listening on port
        //     <port>.  The server has a maximum pending (incoming) connection
        //     queue of length <backlog>.
        // Required arguments:
        //     port: listening port
        //     backlog: maximum length of pending connection queue
        // Optional arguments:
        //     servint: execution interval of the transfer server, default 1 second
        //     workint: execution interval of the transfer worker, default 1 second
        //     sz: buffer size of the transfer worker, default 65536
        String[] args = command.split(" ");
        if (args.length < 3 || args.length > 6 || !args[0].equals("server")) {
            return false;
        }

        try {
            int port = Integer.parseInt(args[1]);
            int backlog = Integer.parseInt(args[2]);
            long servint =
                args.length >= 4 ?
                Integer.parseInt(args[3]) :
                TransferServer.DEFAULT_SERVER_INTERVAL;
            long workint =
                args.length >= 5 ?
                Integer.parseInt(args[4]) :
                TransferServer.DEFAULT_WORKER_INTERVAL;
            int sz =
                args.length == 6 ?
                Integer.parseInt(args[5]) :
                TransferServer.DEFAULT_BUFFER_SZ;
             // TCP connection book keeping:
            if(tcpMan.addConnection(port, backlog, servint, workint, sz) < 0){
            	this.logError("Port " + port + " is already binded to a socket.");
            }
            /*
            TCPSock sock = this.tcpMan.socket();
            sock.bind(port);
            sock.listen(backlog);
            
            TransferServer server = new
               TransferServer(manager, this, sock, servint, workint, sz);
            server.start();
            logOutput("server started, port = " + port);
			*/
            return true;
        } catch (Exception e) {
            logError("Exception: " + e);
        }

        return false;
    }
    
    // ----------------------------Other useful functions----------------------------------:
    // Decrements the TTL of all link state packets this node currently has.
    private void decreaseLSTTL(){
    	Enumeration <Integer> trvrs = this.lsttl.keys();
    	while(trvrs.hasMoreElements()){
    		Integer x = trvrs.nextElement();
    		if(lsttl.get(x) > 0)
    			this.lsttl.put(x, lsttl.get(x) - 1);
    	}
    }
    // Keep in mind that this version of Dijkstra only works if cost is solely just the hop
    // count.
    private void useDijkstra(){
    	lsmtx.lock();
    	try{
    		// local Hashtables to be used for the "confirmed" and "tentative" routes
    		Hashtable <Integer, Integer> tentHop = new Hashtable <Integer, Integer>();
        	Hashtable <Integer, Integer> tentCost = new Hashtable <Integer, Integer>();
        	Hashtable <Integer, Integer> confHop = new Hashtable <Integer, Integer>();
    		Hashtable <Integer, Integer> confCost = new Hashtable <Integer, Integer>();
    		// Initially, tentative will contain this node only.
    		tentHop.put(this.addr, this.addr);
    		tentCost.put(this.addr, 0);
    		confHop.put(this.addr, this.addr);
    		confCost.put(this.addr, 0);
    		int cct = 0;
    		// We keep going until tentative list is completely empty
    		while(!tentHop.isEmpty()){
    			Enumeration <Integer> trvrs = tentHop.keys();
    			while(trvrs.hasMoreElements()){
    				// Anything removed from tentative is confirmed:
    				Integer x = trvrs.nextElement();
    				confHop.put(x, tentHop.get(x));
    				confCost.put(x, tentCost.get(x));
    				tentHop.remove(x);
    				// "expand" the current node x:
    				int [] nlst = lsrecv.get(x).getNeighbors();
    				cct++;
    				// For all of x's neighbors...
    				for(int y = 0; y < nlst.length; y++){
    					// If this isn't in tentative yet, add it only if its cost is less than
    					// what's currently stored in its current confirmed info, or if it's not
    					// confirmed yet.
    					if( ( !tentCost.containsKey(nlst[y]) && !confHop.containsKey(nlst[y]) )
    						|| ( !tentCost.containsKey(nlst[y]) && (confHop.get(nlst[y]) > cct) ) ){
    						tentCost.put(nlst[y], cct);
    						if(cct == 1)
    							tentHop.put(nlst[y], nlst[y]);
    						else
    							tentHop.put(nlst[y], confHop.get(x));
    						tentCost.put(nlst[y], confCost.get(x) + 1);
    					}
    					// Else, put it in tentative if its cost is less than what's currently in
    					// tentative.
    					else if(tentCost.get(nlst[y]) > (confCost.get(x) + 1)){
    						tentCost.put(nlst[y], (confCost.get(x) + 1));
    						tentHop.put(nlst[y], confHop.get(x));
    					}
    				}
    			}
    		}
    		// Once routing table is fully calculated, overwrite the current routing table
    		rtmtx.lock();
    		try{
    			this.destHop = confHop;
    			this.destCost = confCost;
    		}finally{
    			rtmtx.unlock();
    		}
    	}finally{
    		lsmtx.unlock();
    	}
    }
    // Looks up the name hashtable; translates a string address into the proper integer address
    private int nameTranslate(String saddr){
    	npmtx.lock();
    	try{
	    	Enumeration <Integer> trvrs = lsname.keys();
	    	while(trvrs.hasMoreElements()){
	    		Integer x = trvrs.nextElement();
	    		if(saddr.equals(lsname.get(x)) || saddr.equals(x.toString())){
	    			return x;
	    		}
	    	}
	    	return -1;
    	}finally{
    		npmtx.unlock();
    	}
    }
    // Closes TCP connections:
    public void closeTCPConnection(int portNo){
    	tcpMan.initiateShutdown(portNo);
    }
}
