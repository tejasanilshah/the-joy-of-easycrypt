> Program testing can be used to show the presence of bugs, but never to show their absence!
> --Edsger W. Dijkstra

Building reliable software is extremely hard. In order to provide guarantees of a software's reliability there are plenty of different approaches that we employ, ranging from testing to various software building methodologies. However, these are among the weakest guarantees that we can provide or are simply best practices that can ensure some level of reliability.

With the explosion of software applications being used, bad software has also been the source of literal explosions. For instance, NASA lost its Mars Climate Orbiter in 1998 due to a bug in converting units from the Imperial system to the SI system. More recently, bad software led to the death of 346 people onboard two Boeing 737 MAX airplanes which crashed in 2018 and 2019. Bad software has proven to be extremely costly.

Now, on the opposite end of the spectrum of software reliability guarantees lies the field of formal verification. The core idea behind formal verification of software is to provide mathematical guarantees of program behaviour on the basis of specifications. It grew out of the field of formal mathematical proofs, and later computer-aided mathematical proofs. So, it rests on the firm foundations of formal logic and reasoning, and formal mathematical proofs.

We will take look at how the field developed, and trace the need for formal verification in cryptography. Later we build up to working with EasyCrypt, which is a tool that allows us to verify game-based cryptographic proofs.

## Formal Verification: A brief history
The ideas of formal verification can be traced back to the 17th century and Leibniz's ideas about characteristica universalis, a universal conceptual language that could be used to solve the logical problems. However, we do not need to go that far back, for our intents and purposes computer-aided math came into limelight with the famous four colour theorem being proven with the help of computers by Appel and Haken [cite]. 

The problem statement is quite simple and elegant. It says,\enquote{Any planar map can be coloured with only four colours}. The computer-aided proof of the problem attracted plenty of criticism since it was done by performing an exhaustive case analysis of a billion cases. This simply means the computer went through every single case that could arise when trying to colour a map, and came back saying that four colours is all it takes. So for an elegant problem the proposed computer-aided proof simply felt like using a sledgehammer to crack a seemingly innocent nut, and a lot of mathematicians at the time cried foul.

Criticism aside, proving the four colour theorem with the help of a computer set off more work and efforts in the field as the ideas from that endeavour were later distilled. Other mathematicians like Robertson, et al and Gonthier, came up with more “elegant” proofs that first reduced the cases by a factor of four [cite], and then to a meagre 633 cases [cite] respectively.

## Formal Verification in Cryptography

As the field of formal verification in math took off, and got established over the years, there was a problem brewing in the academic circles dealing with cryptography. At its core modern cryptography is math, and to demonstrate different security properties of protocols we come up with mathematical proofs and guarantees about them. As the field advanced it ran into the problem of these proofs being too complicated for humans to go through. This problem can be best illustrated with this excerpt from [Halevi 09]:

"The problem is that as a community, we generate more proofs than we carefully verify (and as a consequence some of our published proofs are incorrect). I became acutely aware of this when I wrote my EME* paper [Hal04]. After spending a considerable effort trying to simplify the proof, I ended up with a 23-page proof of security for a — err — marginally useful mode-of-operation for block ciphers. Needless to say, I do not expect anyone in his right mind to even read the proof, let alone carefully verify it."

In the paper, Halevi highlights that cryptography as a field has advanced to the point where the proofs are so complex that the field could benefit from automation, or at the very least some help from machines. In a way these; automated and computer assisted, are the two approaches that are possible in the field of formal verification of cryptography. Since the development of the software tools needed for formal verification of cryptography, the term computer-aided cryptography is used interchangeably with formally verified cryptography.

## What is Computer-aided Cryptography?

At this point, it is a good idea to read Sec 1.1 of JoC to get an understanding of what cryptography is, and what it is not. To summarise and add to the ideas from JoC, modern cryptography deals with three main problems of communication. They are:

1. *Privacy*: Protecting information from being accessed by unauthorised parties
2. *Integrity*: Protecting information from being tampered or altered
3. *Authenticity*: Making sure the information is from an authentic source

Each of these properties can be defined as mathematical properties of information, and to state that a cryptographic protocol protects a certain property is to prove that the information possesses that mathematical property. Given that the proofs can be complicated and hard to follow, the idea of using computers to verify the proofs comes in here.

To illustrate this idea better, let us first meet Alice, Bob and Eve. We will assume that Alice wants to send a message to Bob and wants the communication to be private. While Eve wants to eavesdrop on their communication. One way to prove that a system of communication is secure is to think of Alice, Bob and Eve playing a game where the objective of the game for Alice and Bob is to communicate in a way that Eve can't differentiate between the messages and a random string of characters. This would mean that Eve can extract just as much information from an intercepted message as they would be able to extract from random noise, implying that the communication is private. This game can be modelled and proven mathematically. Then we can use tools to formally verify these proofs on a computer.

These ideas and the games that Alice, Bob and Eve play, are essentially the cornerstones of provable and verifiable security.

## Criticism of Computer-aided Cryptography}

Although the need for the field has been well established it faces a number of challenges and has its own shortcomings. The main criticism being that a few big important protocols, such as Bluetooth, and TLS, are verified however they are less likely to discover flaws since these protocols are subject to extensive testing and attack. Whereas the protocols that aren't used to support major industrial applications generally aren't subject to the same level of scrutiny. They only receive limited manual testing. 

Additionally, a high barrier to entry to the field compounds this problem as teams developing protocols can't spend the time and effort required to go through the process of formally verifying them. In the end, the benefits to formal verification can seem marginal as the tools themselves can have flaws, leading to the philosophical conundrum of “Who will guard the guards themselves?”

As a response to these challenges the field offers the following rebuttals:
1. The field is still new and the tooling is undergoing active development. Once the tools mature and are easier to use we can expect the industry to move in the direction of requiring formal verification for protocols to be put into use. For instance, the development of the 5G protocol happened in close collaboration with the formal verification community and is an encouraging move in the right direction
2. Even though the tools might have flaws, the point to note here is that it would be exceptionally hard for a mathematical proof to be wrong and also getting past a formal verification check. So a flawed tool already provides better security compared to a human verified proof. The standard to beat remains a highly specialised set of human eyes verifying a mathematical proof. The argument of who guards the guards themselves already applies to the current situation, and what is being proposed is a major improvement
3. The high barrier to entry remains a problem to be solved and works like this one aim to address this challenge

All in all there is plenty of work left to do in the field.