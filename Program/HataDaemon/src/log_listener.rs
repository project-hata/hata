
// use std::net::TcpListener;
// use std::net::TcpStream;
use std::io::Read;
use std::convert::From;

use crate::error::*;

// extern crate alloc;
// use alloc::sync::Arc;
use std::sync::{Arc, Mutex};

// fn handle_client(mut stream: TcpStream) -> Result<(),HataError> {
//     let mut buffer = Vec::new();

//     // read the whole file
//     stream.read_to_end(&mut buffer)?;
//     let text = std::str::from_utf8(&buffer).to_owned()?;
//     println!("{}", text);

//     Ok(())
// }


// pub fn listen(messages: Arc<Vec<String>>) -> Result<(),HataError> {
//     let listener = TcpListener::bind("127.0.0.1:49999")?;

//     // accept connections and process them serially
//     for stream in listener.incoming() {
//         handle_client(stream?)?;
//     }
//     Ok(())
// }


////////////////////////////////////////////////////////////////////
use tokio::net::TcpListener;
use tokio::io::{AsyncReadExt, AsyncWriteExt};

pub async fn listen(messages: Arc<Mutex<Vec<String>>>) -> Result<(), Box<dyn std::error::Error>> {
    let listener = TcpListener::bind("127.0.0.1:49999").await?;

    tokio::spawn(async move {

        loop {
            let (mut socket, _) = listener.accept().await.unwrap();

            let m1 = messages.clone();

            tokio::spawn(async move {
                // let mut buf = [0; 1024];
                let mut buffer = Vec::new();

                // In a loop, read data from the socket and write the data back.
                loop {

                    let n = match socket.read_to_end(&mut buffer).await {
                        // socket closed
                        Ok(n) if n == 0 => return,
                        Ok(n) => n,
                        Err(e) => {
                            eprintln!("failed to read from socket; err = {:?}", e);
                            return;
                        }
                    };
                    let text = match std::str::from_utf8(&buffer).to_owned() {
                        Ok(text) => text,
                        Err(e) => {
                            eprintln!("failed to read from socket; err = {:?}", e);
                            return;
                        }
                    };
                    let mut ml = m1.lock().unwrap();
                    ml.push(text.to_owned());

                        // .push(text.to_owned());
                    println!("got message: {text}");

                    // // Write the data back
                    // if let Err(e) = socket.write_all(&buf[0..n]).await {
                    //     eprintln!("failed to write to socket; err = {:?}", e);
                    //     return;
                    // }
                }
            });
        }
        // let res : Result<(), Box<dyn std::error::Error>> = Ok(());
        // res

    }



    );
    Ok(())

}


