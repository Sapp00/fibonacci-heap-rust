pub trait Min{
    fn min_value() -> Self;
}

impl Min for u8{
    fn min_value() -> u8{
        std::u8::MIN
    }
}

impl Min for u16{
    fn min_value() -> u16{
        std::u16::MIN
    }
}

impl Min for u32{
    fn min_value() -> u32{
        std::u32::MIN
    }
}

impl Min for u64{
    fn min_value() -> u64{
        std::u64::MIN
    }
}

impl Min for usize{
    fn min_value() -> usize{
        std::usize::MIN
    }
}

impl Min for i8{
    fn min_value() -> i8{
        std::i8::MIN
    }
}

impl Min for i16{
    fn min_value() -> i16{
        std::i16::MIN
    }
}

impl Min for i32{
    fn min_value() -> i32{
        std::i32::MIN
    }
}

impl Min for i64{
    fn min_value() -> i64{
        std::i64::MIN
    }
}

impl Min for f32{
    fn min_value() -> f32{
        std::f32::MIN
    }
}

impl Min for f64{
    fn min_value() -> f64{
        std::f64::MIN
    }
}