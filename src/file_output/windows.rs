use std::fs::File;
use std::io;
use std::os::windows::io::AsRawHandle;
use std::ptr;

use windows_sys::Win32::Foundation::LocalFree;
use windows_sys::Win32::Security::Authorization::{GetSecurityInfo, SE_FILE_OBJECT};
use windows_sys::Win32::Security::{
    DACL_SECURITY_INFORMATION, GROUP_SECURITY_INFORMATION, GetLengthSid,
    GetSecurityDescriptorControl, OWNER_SECURITY_INFORMATION, PSECURITY_DESCRIPTOR,
    SE_DACL_PROTECTED,
};

#[derive(PartialEq, Eq)]
pub(super) struct Security {
    owner: Vec<u8>,
    group: Vec<u8>,
    dacl: Option<Vec<u8>>,
    protected: bool,
}

impl Security {
    pub(super) fn read(file: &File) -> io::Result<Self> {
        let mut owner = ptr::null_mut();
        let mut group = ptr::null_mut();
        let mut dacl = ptr::null_mut();
        let mut descriptor = ptr::null_mut();
        // GetSecurityInfo owns the returned allocation; the other pointers borrow it.
        let error = unsafe {
            GetSecurityInfo(
                file.as_raw_handle(),
                SE_FILE_OBJECT,
                OWNER_SECURITY_INFORMATION | GROUP_SECURITY_INFORMATION | DACL_SECURITY_INFORMATION,
                &mut owner,
                &mut group,
                &mut dacl,
                ptr::null_mut(),
                &mut descriptor,
            )
        };
        if error != 0 {
            return Err(io::Error::from_raw_os_error(error as i32));
        }
        let descriptor = Descriptor(descriptor);
        let mut control = 0;
        let mut revision = 0;
        // The descriptor and all its components remain alive until the copies finish.
        unsafe {
            if GetSecurityDescriptorControl(descriptor.0, &mut control, &mut revision) == 0 {
                return Err(io::Error::last_os_error());
            }
            let copy_sid = |sid: windows_sys::Win32::Security::PSID| {
                if sid.is_null() {
                    Vec::new()
                } else {
                    std::slice::from_raw_parts(sid.cast::<u8>(), GetLengthSid(sid) as usize)
                        .to_vec()
                }
            };
            Ok(Self {
                owner: copy_sid(owner),
                group: copy_sid(group),
                dacl: (!dacl.is_null()).then(|| {
                    std::slice::from_raw_parts(dacl.cast::<u8>(), (*dacl).AclSize as usize).to_vec()
                }),
                protected: control & SE_DACL_PROTECTED != 0,
            })
        }
    }
}

struct Descriptor(PSECURITY_DESCRIPTOR);

impl Drop for Descriptor {
    fn drop(&mut self) {
        // The allocation was returned by GetSecurityInfo and is released exactly once.
        unsafe {
            LocalFree(self.0);
        }
    }
}
