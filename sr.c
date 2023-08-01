#include <stdlib.h>
#include <stdio.h>
#include <stdbool.h>
#include "emulator.h"
#include "sr.h"

/* ******************************************************************
   Selective Repeat protocol.
**********************************************************************/

#define RTT 16.0      /* round trip time.  MUST BE SET TO 16.0 when submitting assignment */
#define WINDOWSIZE 6  /* the maximum number of buffered unacked packet */
#define SEQSPACE 12   /* the min sequence space for SR must be at least windowsize*2 */
#define NOTINUSE (-1) /* used to fill header fields that are not being used */

/* generic procedure to compute the checksum of a packet.  Used by both sender and receiver
   the simulator will overwrite part of your packet with 'z's.  It will not overwrite your
   original checksum.  This procedure must generate a different checksum to the original if
   the packet is corrupted.
*/
int ComputeChecksum(struct pkt packet)
{
    int checksum = 0;
    int i;

    checksum = packet.seqnum;
    checksum += packet.acknum;
    for (i = 0; i < 20; i++)
        checksum += (int)(packet.payload[i]);

    return checksum;
}

bool IsCorrupted(struct pkt packet)
{
    if (packet.checksum == ComputeChecksum(packet))
        return (false);
    else
        return (true);
}

/********* Sender (A) variables and functions ************/

static struct pkt buffer[WINDOWSIZE]; /* array for storing packets waiting for ACK */
static int windowfirst, windowlast;   /* array indexes of the first/last packet awaiting ACK */
static int windowcount;               /* the number of packets currently awaiting an ACK */
static int A_nextseqnum;              /* the next sequence number to be used by the sender */
static bool acked[SEQSPACE];          /* array to keep track of which packets have been ACKed */
static bool has_stopped;              /* flag to indicate if timer has been stopped */

/********* timer for selective repeat ************/
typedef struct timer_node
{
    int seqnum;
    double start_time;
    struct timer_node *next;
} timer;

timer *timer_head = NULL;

/* called from layer 5 (application layer), passed the message to be sent to other side */
void A_output(struct msg message)
{
    struct pkt sendpkt;
    int i;

    /* if not blocked waiting on ACK */
    if (windowcount < WINDOWSIZE)
    {
        if (TRACE > 1)
            printf("----A: New message arrives, send window is not full, send new messge to layer3!\n");

        /* create packet */
        sendpkt.seqnum = A_nextseqnum;
        sendpkt.acknum = NOTINUSE;
        for (i = 0; i < 20; i++)
            sendpkt.payload[i] = message.data[i];
        sendpkt.checksum = ComputeChecksum(sendpkt);

        /* put packet in window buffer */
        /* windowlast will always be 0 for alternating bit; but not for GoBackN */
        windowlast = (windowlast + 1) % WINDOWSIZE;
        buffer[windowlast] = sendpkt;
        windowcount++;

        /* send out packet */
        if (TRACE > 0)
            printf("Sending packet %d to layer 3\n", sendpkt.seqnum);
        tolayer3(A, sendpkt);

        /* set corresponding acked record as false*/
        acked[sendpkt.seqnum] = false;

        /* start timer if first packet in window */
        if (windowcount == 1)
            starttimer(A, RTT);

        /* get next sequence number, wrap back to 0 */
        A_nextseqnum = (A_nextseqnum + 1) % SEQSPACE;
    }
    /* if blocked,  window is full */
    else
    {
        if (TRACE > 0)
            printf("----A: New message arrives, send window is full\n");
        window_full++;
    }
}

/* called from layer 3, when a packet arrives for layer 4
   In this practical this will always be an ACK as B never sends data.
*/
void A_input(struct pkt packet)
{

    /* if received ACK is not corrupted */
    if (!IsCorrupted(packet))
    {
        if (TRACE > 0)
            printf("----A: uncorrupted ACK %d is received\n", packet.acknum);
        total_ACKs_received++;

        /* check if new ACK or duplicate */
        if (windowcount != 0)
        {
            int seqfirst = buffer[windowfirst].seqnum;
            int seqlast = buffer[windowlast].seqnum;
            /* check case when seqnum has and hasn't wrapped and hasn't received */
            /* review this later */
            if ((((seqfirst <= seqlast) && (packet.acknum >= seqfirst && packet.acknum <= seqlast)) ||
                 ((seqfirst > seqlast) && (packet.acknum >= seqfirst || packet.acknum <= seqlast))) &&
                !acked[packet.acknum])
            {

                /* packet is a new ACK */
                if (TRACE > 0)
                    printf("----A: ACK %d is not a duplicate\n", packet.acknum);
                new_ACKs++;

                /* marked the corresponding packet as acked */
                acked[packet.acknum] = true;

                has_stopped = false;
                /* stop timer if the window need to slide*/
                if (acked[buffer[windowfirst].seqnum])
                {
                    stoptimer(A);
                    has_stopped = true;
                }

                /* slide window and modify window count */
                while (acked[buffer[windowfirst].seqnum] && windowcount > 0)
                {
                    windowfirst = (windowfirst + 1) % WINDOWSIZE;
                    windowcount--;
                    /*printf("----A: sliding window, windowfirst is %d, windowlast is %d, windowcount is %d\n", windowfirst, windowlast, windowcount);*/
                }

                /* start timer again if there are still more unacked packets in window */
                if (windowcount > 0 && has_stopped)
                {
                    starttimer(A, RTT);
                }
            }
        }
        else if (TRACE > 0)
            printf("----A: duplicate ACK received, do nothing!\n");
    }
    else if (TRACE > 0)
        printf("----A: corrupted ACK is received, do nothing!\n");
}

/* called when A's timer goes off */
void A_timerinterrupt(void)
{
    if (TRACE > 0)
        printf("----A: time out,resend packets!\n");

    if (TRACE > 0)
        printf("---A: resending packet %d\n", (buffer[(windowfirst) % WINDOWSIZE]).seqnum);

    tolayer3(A, buffer[(windowfirst) % WINDOWSIZE]);
    packets_resent++;
    starttimer(A, RTT);
}

/* the following routine will be called once (only) before any other */
/* entity A routines are called. You can use it to do any initialization */
void A_init(void)
{
    /* initialise A's window, buffer and sequence number */
    A_nextseqnum = 0; /* A starts with seq num 0, do not change this */
    windowfirst = 0;
    windowlast = -1; /* windowlast is where the last packet sent is stored.
             new packets are placed in winlast + 1
             so initially this is set to -1
           */
    windowcount = 0;
}

/********* Receiver (B)  variables and procedures ************/
static struct pkt recv_buffer[SEQSPACE]; /* buffer of receiver to store packets */
static int expectedseqnum;               /* expected sequence number of the next packet */
static int B_nextseqnum;                 /* next sequence number to be sent to A */
static int last_window_seq;              /* last sequence number that within the receive window */
static bool received[SEQSPACE];          /* array to keep track of which packets have been received */

/* check if the arriving packet is within the current window */
bool is_within_window(int seqnum)
{
    /* if the receive window has wrapped */
    if (expectedseqnum < last_window_seq)
    {
        if (seqnum >= expectedseqnum && seqnum <= last_window_seq)
            return true;
        else
            return false;
    }
    /* if the receive window has not wrapped */
    else
    {
        if (seqnum >= last_window_seq || seqnum <= expectedseqnum)
        {
            return true;
        }
        else
        {
            return false;
        }
    }
}

/* check if the arriving packet is within the last window */
bool is_within_last_window(int seqnum)
{
    int last_window_first = (expectedseqnum - WINDOWSIZE) % SEQSPACE;
    int last_window_last = expectedseqnum - 1;

    /* if the last receive window has wrapped */
    if (last_window_first < last_window_last)
    {
        if (seqnum >= last_window_first && seqnum <= last_window_last)
            return true;
        else
            return false;
    }
    /* if the last receive window has not wrapped */
    else
    {
        if (seqnum >= last_window_last || seqnum <= last_window_first)
        {
            return true;
        }
        else
        {
            return false;
        }
    }
}

/* called from layer 3, when a packet arrives for layer 4 at B*/
void B_input(struct pkt packet)
{
    struct pkt sendpkt;

    /* if the packet is not corrupted and is within the expected window, send the corresponding ack */
    /* if not corrupted and received packet is in order */
    if (!IsCorrupted(packet))
    {
        packets_received++;

        /* if the packet is within the expected window or within the last window, send an ACK*/
        if (is_within_window(packet.seqnum) || is_within_last_window(packet.seqnum))
        {
            int i;
            /* send the selective ACK */
            sendpkt.acknum = packet.seqnum;
            sendpkt.seqnum = B_nextseqnum;
            /* we don't have any data to send.  fill payload with 0's */
            for (i = 0; i < 20; i++)
                sendpkt.payload[i] = '0';

            /* computer checksum */
            sendpkt.checksum = ComputeChecksum(sendpkt);
            B_nextseqnum = (B_nextseqnum + 1) % 2;

            if (TRACE > 0)
                printf("----B: packet %d is correctly received, send ACK!\n", sendpkt.acknum);
            /* send out the ACK */
            tolayer3(B, sendpkt);

            /* if the packet is within the window, buffer it*/
            if (is_within_window(packet.seqnum))
            {
                /* if the packet is not a duplicate, buffer it */
                if (!received[packet.seqnum])
                {
                    /* if it is not duplicated, buffer the packet */
                    recv_buffer[packet.seqnum] = packet;
                    received[packet.seqnum] = true;

                    /* if the packet is the expected packet(base number), slide the window and deliver the in order buffer to the application */
                    if (packet.seqnum == expectedseqnum)
                    {
                        /* deliver the in order packets to the application */
                        while (received[expectedseqnum])
                        {
                            tolayer5(B, recv_buffer[expectedseqnum].payload);
                            /* update the expected sequence number */
                            expectedseqnum = (expectedseqnum + 1) % SEQSPACE;
                            /* update the last sequence number */
                            last_window_seq = (last_window_seq + 1) % SEQSPACE;
                            /* update the received array */
                            received[(last_window_seq + 1) % SEQSPACE] = false;
                        }
                    }
                }
            }
        }
    }
}

/* the following routine will be called once (only) before any other */
/* entity B routines are called. You can use it to do any initialization */
void B_init(void)
{
    expectedseqnum = 0;
    B_nextseqnum = -1;
    last_window_seq = WINDOWSIZE - 1;
}

/******************************************************************************
 * The following functions need be completed only for bi-directional messages *
 *****************************************************************************/

/* Note that with simplex transfer from a-to-B, there is no B_output() */
void B_output(struct msg message)
{
}

/* called when B's timer goes off */
void B_timerinterrupt(void)
{
}
