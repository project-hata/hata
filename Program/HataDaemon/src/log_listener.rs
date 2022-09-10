
use std::net::TcpListener;
use std::net::TcpStream;
use std::io::Read;
use std::convert::From;

use crate::error::*;

fn handle_client(mut stream: TcpStream) -> Result<(),HataError> {
    let mut buffer = Vec::new();

    // read the whole file
    stream.read_to_end(&mut buffer)?;
    let text = std::str::from_utf8(&buffer).to_owned()?;
    println!("{}", text);

    Ok(())
}


pub fn listen() -> Result<(),HataError> {
    let listener = TcpListener::bind("127.0.0.1:49999")?;

    // accept connections and process them serially
    for stream in listener.incoming() {
        handle_client(stream?)?;
    }
    Ok(())
}


